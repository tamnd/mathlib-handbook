---
title: Lists without duplicates, permutations and dedup
kind: theory
modules:
  - Mathlib.Data.List.Nodup
  - Mathlib.Data.List.NodupEquivFin
  - Mathlib.Data.List.Dedup
  - Mathlib.Data.List.Perm.Basic
  - Mathlib.Data.List.Perm.Lattice
  - Mathlib.Data.List.Perm.Subperm
  - Mathlib.Data.List.Permutation
  - Mathlib.Data.List.Lattice
explains:
  E3: [List.nodup_iff_count_le_one, List.nodup_iff_injective_get, List.Nodup.getEquiv, List.Nodup.getEquivOfForallMemList, List.nodup_dedup, List.mem_dedup, List.dedup_eq_self, List.Perm.foldr_eq, List.subperm_iff_count, List.length_permutations, List.mem_permutations, List.count_bagInter]
  E2: [List.nodup_iff_sublist, List.count_eq_one_of_mem, List.not_nodup_pair, List.Nodup.union, List.Nodup.inter, List.Nodup.diff, List.nodup_flatten, List.Nodup.product, List.getEquivOfForallCountEqOne, List.sublist_iff_exists_fin_orderEmbedding_get_eq, List.dedup_cons_of_mem, List.dedup_cons_of_notMem, List.dedup_idem, List.dedup_append, List.Perm.dedup, List.nodup_iff_le_length_dedup, List.instIsEquivPerm, List.instIsPreorderSubperm, List.map_perm_map_iff, List.perm_replicate_append_replicate, List.subperm_iff, List.Nodup.subperm, List.nodup_permutations, List.Perm.permutations, List.perm_permutations_iff, List.length_permutations'Aux, List.mem_permutations', List.permutations_perm_permutations', List.Perm.bagInter, List.Perm.inter_append, List.forall_mem_union]
  E1: auto
families: []
requires: [V01.C03, V03.C02, V03.C04, V33.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lists without duplicates, permutations and dedup

### Overview

A list records its entries in an order and with their multiplicities. Two coarser views of a list are central in Mathlib. The first view forgets the order: two lists are permutations of each other if one is a rearrangement of the other. The multisets of Mathlib are the quotient of lists by this relation. The second view also forgets the multiplicity, and lists without duplicates are the representatives of the finite sets. This section studies the predicate `Nodup`, the bijection between a list without duplicates and `Fin n`, the operation `dedup` that removes the duplicates, the permutation relation with its characterization by counts, the relation `Subperm`, the list of all permutations with its length $n!$, and the operations of union, intersection and difference.

The predicates `Nodup`, `Perm` and `Subperm` and most of their basic API are in the core library. Mathlib adds the equivalences, the counting results and the list of all permutations.

### Definitions

**Definition (Nodup).** `l.Nodup` means that the entries of $l$ are pairwise distinct: `Nodup l` is `Pairwise (· ≠ ·) l`. So $[\,]$ has no duplicates, and $a :: l$ has none if and only if $a \notin l$ and $l$ has none.

**Definition (Permutation).** The relation $l_1 \sim l_2$ (`List.Perm`) is the inductive relation with four rules: $[\,] \sim [\,]$; if $l_1 \sim l_2$ then $x :: l_1 \sim x :: l_2$; $y :: x :: l \sim x :: y :: l$ (swap); and if $l_1 \sim l_2$ and $l_2 \sim l_3$ then $l_1 \sim l_3$. So the permutations of $l$ are the lists obtained from $l$ by a finite sequence of swaps of neighbours.

**Definition (Subperm).** $l_1 <\!+\!\sim\ l_2$ (`List.Subperm`) means that some $l$ with $l \sim l_1$ is a sublist of $l_2$. It is the relation "$l_1$ is contained in $l_2$ as a multiset".

**Definition (Dedup).** `dedup l` is `pwFilter (· ≠ ·) l`. On $a :: l$ it drops $a$ if $a$ occurs again in $l$, and it keeps $a$ in front of `dedup l` otherwise. So `dedup` keeps the last occurrence of each entry.

**Definition (All permutations).** `permutations l` is the list of all permutations of $l$. Its definition uses an efficient auxiliary function. The specification `permutations' l` is simpler: `permutations' [] = [[]]`, and `permutations' (t :: ts)` takes each list $s$ of `permutations' ts` and inserts $t$ at each of the $|s| + 1$ positions of $s$ (`permutations'Aux t s`). The two lists are permutations of each other (`permutations_perm_permutations'`).

**Definition (Union, intersection, difference).** For a type with decidable equality, `l₁ ∪ l₂` inserts the entries of $l_1$ into $l_2$ from the right, and `insert a l` puts $a$ in front of $l$ only if $a \notin l$. `l₁ ∩ l₂` keeps the entries of $l_1$ that are in $l_2$. `l₁.diff l₂` erases from $l_1$ one occurrence of each entry of $l_2$, and `l₁.bagInter l₂` is the intersection of multisets.

### Theorems and proofs

**Theorem (Nodup by counts and by positions).** $l$ has no duplicates if and only if `count a l ≤ 1` for each $a$, if and only if the map $i \mapsto l_i$ from `Fin |l|` to $\alpha$ is injective.

*Proof.* Induction on $l$. For $[\,]$ all counts are $0$ and `Fin 0` is empty. For $a :: l$, `count b (a :: l)` is `count b l` for $b \neq a$, and `count a l + 1` for $b = a$. So all counts are at most $1$ if and only if the counts of $l$ are at most $1$ and `count a l = 0`, that is, $a \notin l$. This is the rule for `Nodup (a :: l)`. For the positions: the entries of $a :: l$ are $a$ at $0$ and $l_i$ at $i + 1$. The map is injective if and only if the map of $l$ is injective and $a \neq l_i$ for each $i$, that is, $a \notin l$. $\square$

**Theorem (A list without duplicates is a copy of Fin n).** If $l$ has no duplicates, then $i \mapsto l_i$ is a bijection from `Fin |l|` onto the subtype of the members of $l$ (`Nodup.getEquiv`). If also each element of $\alpha$ is in $l$, it is a bijection `Fin |l| ≃ α` (`Nodup.getEquivOfForallMemList`).

*Proof.* The map is injective by the previous theorem. It is surjective, because $x \in l$ means that $x = l_i$ for some position $i < |l|$. The inverse sends $x$ to `idxOf x l`, the first position of $x$, and $l_{\operatorname{idxOf} x\, l} = x$ for $x \in l$. If each element is in $l$, the subtype of the members is all of $\alpha$. $\square$

This is how Mathlib proves that a type with a list of all its elements without duplicates is finite with $|l|$ elements.

**Proposition (Dedup).** `dedup l` has no duplicates, has the same members as $l$, and is a sublist of $l$. `dedup l = l` if and only if $l$ has no duplicates.

*Proof.* Induction on $l$, by the two rules of `dedup`. For $[\,]$ the claims hold. For $a :: l$ with $a \in l$, `dedup (a :: l) = dedup l` (`dedup_cons_of_mem`), which has the members of $l$, and these are the members of $a :: l$ since $a \in l$. For $a \notin l$, `dedup (a :: l) = a :: dedup l` (`dedup_cons_of_notMem`), and $a \notin \operatorname{dedup} l$ because the members are those of $l$; so it has no duplicates. In both cases it is a sublist. If $l$ has no duplicates, then the second rule applies at each step, and `dedup l = l`. Conversely, `dedup l = l` gives `Nodup l` from the first claim. $\square$

**Theorem (Permutations by counts).** For a type with decidable equality, $l_1 \sim l_2$ if and only if `count a l₁ = count a l₂` for each $a$.

*Proof.* Suppose $l_1 \sim l_2$, and use induction on the rules. The rule for $[\,]$ and the rule for $x ::$ preserve the equality of counts, the swap does not change a count, and the equality is transitive. Conversely, use induction on $l_1$ for all $l_2$. If $l_1 = [\,]$, then all counts of $l_2$ are $0$, so $l_2 = [\,]$. If $l_1 = a :: l$, then `count a l₂ = count a l + 1 ≥ 1`, so $a \in l_2$, and $l_2 \sim a :: (l_2.\operatorname{erase} a)$ by the core lemma `perm_cons_erase`. The counts of $l$ and of $l_2.\operatorname{erase} a$ are equal: for $b \neq a$ the erasure does not change the count, and for $b = a$ both sides lose $1$. By the hypothesis, $l \sim l_2.\operatorname{erase} a$, so $a :: l \sim a :: (l_2.\operatorname{erase} a) \sim l_2$. $\square$

The core library states this as `perm_iff_count`. It gives a decision procedure for $\sim$, and it shows that $\sim$ is an equivalence relation (`instIsEquivPerm`), the relation of the quotient `Multiset α`.

**Theorem (Subperm by counts).** $l_1 <\!+\!\sim\ l_2$ if and only if `count a l₁ ≤ count a l₂` for each $a$.

*Proof.* If $l \sim l_1$ and $l <\!+\ l_2$, then the counts of $l_1$ are those of $l$, and a sublist has smaller counts. Conversely, use induction on $l_1$ for all $l_2$. For $[\,]$, the empty list is a sublist of each list. For $a :: l$, the count of $a$ in $l_2$ is at least $1$, so $l_2 \sim a :: l_2'$ with $l_2' = l_2.\operatorname{erase} a$, and the counts of $l$ are at most those of $l_2'$. By the hypothesis, $l <\!+\!\sim\ l_2'$, so $a :: l <\!+\!\sim\ a :: l_2'$, and the permutation $a :: l_2' \sim l_2$ gives $a :: l <\!+\!\sim\ l_2$. $\square$

A list without duplicates that is contained in $l_2$ as a set is contained in it as a multiset (`Nodup.subperm`), since its counts are at most $1$.

**Theorem (Folds are invariant).** If $f \colon \alpha \to \beta \to \beta$ is left commutative, that is, $f\,a\,(f\,b\,c) = f\,b\,(f\,a\,c)$, and $l_1 \sim l_2$, then `foldr f b l₁ = foldr f b l₂`.

*Proof.* Induction on the rules of $\sim$, for all $b$. The rule for $[\,]$ is trivial. For $x :: l_1 \sim x :: l_2$, both sides are $f\,x\,(\operatorname{foldr} f\, b\, l_i)$, equal by the hypothesis. For the swap, $\operatorname{foldr} f\, b\,(y :: x :: l) = f\,y\,(f\,x\,c)$ with $c = \operatorname{foldr} f\, b\, l$, and left commutativity turns it into $f\,x\,(f\,y\,c)$. Transitivity composes the equalities. $\square$

This theorem is why a sum or a product over a multiset is well defined.

**Theorem (All permutations).** $s \in \operatorname{permutations} t$ if and only if $s \sim t$, and `permutations t` has $|t|!$ entries. If $t$ has no duplicates, neither has `permutations t`.

*Proof.* Prove the claims for `permutations'`; the list `permutations t` is a permutation of it, so it has the same members and the same length. Membership: by induction on $t$, each list of `permutations' t` is $t$ with its entries inserted one by one, so it is a permutation of $t$. Conversely, let $s \sim a :: t$. Then $a \in s$, so $s = u \mathbin{+\!\!+} a :: v$, and $u \mathbin{+\!\!+} v \sim t$ by cancellation of $a$. By the hypothesis, $u \mathbin{+\!\!+} v \in \operatorname{permutations'} t$, and $s$ is the insertion of $a$ at position $|u|$ in $u \mathbin{+\!\!+} v$, a member of `permutations'Aux a (u ++ v)`. Length: by induction, `permutations' t` has $n!$ entries, for $n = |t|$, and each is a permutation of $t$, so it has length $n$. The insertion of $a$ gives $n + 1$ lists from each (`length_permutations'Aux`), so there are $n! \cdot (n + 1) = (n + 1)!$ lists. $\square$

**Proposition (Intersection of multisets).** `count a (l₁.bagInter l₂) = min (count a l₁) (count a l₂)`.

*Proof.* Induction on $l_1$ for all $l_2$. The rule of `bagInter` is: on $b :: l_1$, if $b \in l_2$ then put $b$ in front of `l₁.bagInter (l₂.erase b)`, else take `l₁.bagInter l₂`. Write $c_i$ for the counts of $a$. If $b \notin l_2$ and $b = a$, then $c_2 = 0$ and both sides are $0$. If $b \neq a$, the count of $a$ does not change on either side. If $b = a \in l_2$, the left side is $1 + \min(c_1 - 1, c_2 - 1)$, which is $\min(c_1, c_2)$. $\square$

### Examples

**Example (Dedup and counts).** For $l = [1, 2, 1, 3, 2]$: the counts are $2, 2, 1$ for $1, 2, 3$, so $l$ has duplicates. The rules of `dedup` from the left: $1$ occurs again, drop it; $2$ occurs again, drop it; $1$ does not occur again in $[3, 2]$, keep it; $3$ and $2$ are kept. So `dedup l = [1, 3, 2]`, with the last occurrences in their order. The bijection `Fin 3 ≃ {x // x ∈ [1, 3, 2]}` sends $0, 1, 2$ to $1, 3, 2$.

**Example (Permutations of three entries).** `permutations' [3] = [[3]]`. Then `permutations' [2, 3]` inserts $2$ into $[3]$: $[[2, 3], [3, 2]]$. Then $1$ is inserted at the three positions of each: from $[2, 3]$ come $[1, 2, 3]$, $[2, 1, 3]$, $[2, 3, 1]$, and from $[3, 2]$ come $[1, 3, 2]$, $[3, 1, 2]$, $[3, 2, 1]$. These are the $3! = 6$ permutations. The count test confirms $[2, 3, 1] \sim [1, 2, 3]$: each entry occurs once in both.

**Counterexample (Duplicates in the list of permutations).** For $t = [1, 1]$, `permutations t` has $2! = 2$ entries, and both are $[1, 1]$. So the hypothesis `Nodup t` in `nodup_permutations` is necessary, and the number of distinct rearrangements of $t$ is not $|t|!$ in general.

**Example (Union, intersection, difference).** For $l_1 = [1, 1, 2]$ and $l_2 = [1, 2, 2, 3]$: `l₁ ∪ l₂ = [1, 2, 2, 3]`, since $1$ and $2$ are already in $l_2$. `l₁ ∩ l₂ = [1, 1, 2]`, since each entry of $l_1$ is in $l_2$. `l₁.bagInter l₂ = [1, 2]`, with the counts $\min(2, 1) = 1$ and $\min(1, 2) = 1$. `l₁.diff l₂ = [1]`, since one $1$ and the $2$ are erased, and `l₂.diff l₁ = [2, 3]`. Also $l_1 <\!+\!\sim\ l_2$ fails, since $1$ occurs twice in $l_1$ and once in $l_2$.

```lean
example : [1, 2, 1, 3, 2].dedup = [1, 3, 2] := by decide
example : [2, 3, 1].Perm [1, 2, 3] := by decide
example : ([1, 2, 3].permutations).length = 6 := by decide
```

### The library around it

::: mathlib
`List.nodup_iff_count_le_one` · `Mathlib.Data.List.Nodup`

`nodup_iff_count_le_one`, `nodup_iff_injective_get`, `nodup_iff_sublist` (no $[a, a]$ is a sublist), `count_eq_one_of_mem`, `not_nodup_pair`, and the closure lemmas `Nodup.union`, `Nodup.inter`, `Nodup.diff`, `nodup_flatten` and `Nodup.product`.

<?decl List.nodup_iff_count_le_one?>
:::

::: mathlib
`List.Nodup.getEquivOfForallMemList` · `Mathlib.Data.List.NodupEquivFin`

`Nodup.getEquiv`, `Nodup.getEquivOfForallMemList`, `getEquivOfForallCountEqOne`, and `sublist_iff_exists_fin_orderEmbedding_get_eq`, which describes a sublist by an order embedding of positions.

<?decl List.Nodup.getEquivOfForallMemList?>
:::

::: mathlib
`List.dedup_eq_self` · `Mathlib.Data.List.Dedup`

`nodup_dedup`, `mem_dedup`, `dedup_eq_self`, `dedup_idem`, `dedup_append : (l₁ ++ l₂).dedup = l₁ ∪ l₂.dedup`, `Perm.dedup` and `nodup_iff_le_length_dedup`.

<?decl List.dedup_eq_self?>
:::

::: mathlib
`List.Perm.foldr_eq` · `Mathlib.Data.List.Perm.Basic`

`Perm.foldr_eq`, the instances `instIsEquivPerm` and `instIsPreorderSubperm`, `map_perm_map_iff` for injective maps, and `perm_replicate_append_replicate`. `Mathlib.Data.List.Perm.Subperm` has `subperm_iff`, `subperm_iff_count` and `Nodup.subperm`.

<?decl List.Perm.foldr_eq?>
:::

::: mathlib
`List.length_permutations` · `Mathlib.Data.List.Permutation`

`mem_permutations`, `length_permutations`, `nodup_permutations`, `Perm.permutations`, `perm_permutations_iff`, and for the specification `mem_permutations'`, `length_permutations'Aux` and `permutations_perm_permutations'`.

<?decl List.length_permutations?>
:::

::: mathlib
`List.count_bagInter` · `Mathlib.Data.List.Lattice`

`count_bagInter`, `forall_mem_union` and the lemmas on `∪`, `∩` and `bagInter`. `Mathlib.Data.List.Perm.Lattice` has `Perm.bagInter` and `Perm.inter_append`.

<?decl List.count_bagInter?>
:::

Common errors of a learner: The first error is to expect `dedup` to keep the first occurrence; it keeps the last, so `dedup [1, 2, 1] = [2, 1]`. The second error is to read `l₁ ⊆ l₂` as `Subperm`; the subset relation ignores multiplicities. The third error is to expect `l₁ ∪ l₂` to be commutative; it is commutative only up to permutation and only for lists without duplicates. The fourth error is to forget the hypothesis `Nodup` in `nodup_permutations`.

### Exercises

1. (A) Compute `dedup [3, 1, 3, 2, 1]` by the rules. Hint: drop an entry if it occurs again to its right.
2. (A) Decide by counts whether $[1, 2, 2, 3] \sim [2, 3, 1, 2]$ and whether $[1, 2] <\!+\!\sim\ [2, 2, 3]$. Hint: compare the counts of $1$, $2$ and $3$.
3. (A) List `permutations'Aux 0 [1, 2]`. Hint: three lists.
4. (B) Prove that $l_1 \sim l_2$ implies $|l_1| = |l_2|$ and that it preserves `Nodup`. Hint: induction on the rules of $\sim$.
5. (B) Prove that $l_1 \mathbin{+\!\!+} l_2 \sim l_2 \mathbin{+\!\!+} l_1$. Hint: use the count criterion, and the additivity of `count` on append.
6. (B) Prove that $[1, 2, 1]$ occurs twice in `permutations [1, 1, 2]`. Hint: compute `permutations' [1, 1, 2]` by insertion, and use that counts do not change under $\sim$.
7. (C) Prove that $l_1 <\!+\!\sim\ l_2$ and $|l_2| \le |l_1|$ imply $l_1 \sim l_2$. Hint: write $l \sim l_1$ with $l <\!+\ l_2$; a sublist of the same length is the list itself.

### Notes and history

The permutation relation of lists is the basis of the quotient construction of multisets in Mathlib, and lists without duplicates are the basis of finite sets. The count of permutations $n!$ is classical; the method of insertion of the new entry at each position is the usual proof by induction, and Knuth's *The Art of Computer Programming* treats the generation of all permutations in detail.

The Mathlib files are by these authors, read from their headers: `Nodup` by Mario Carneiro and Kenny Lau; `NodupEquivFin` by Yury Kudryashov; `Dedup` by Mario Carneiro; `Perm.Basic`, `Perm.Lattice` and `Perm.Subperm` by Leonardo de Moura, Jeremy Avigad and Mario Carneiro; `Permutation` by Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn and Mario Carneiro; `Lattice` by the same five authors and Kim Morrison.

### Reference

<?reference?>
