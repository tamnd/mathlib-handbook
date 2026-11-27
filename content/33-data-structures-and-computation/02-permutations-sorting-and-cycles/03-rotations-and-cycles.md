---
title: Rotations and cycles
kind: theory
modules:
  - Mathlib.Data.List.Rotate
  - Mathlib.Data.List.Cycle
explains:
  E3: [List.rotate_eq_drop_append_take, List.getElem_rotate, List.rotate_rotate, List.IsRotated, List.instIsEquivIsRotated, List.cyclicPermutations, List.mem_cyclicPermutations_iff, List.Nodup.rotate_eq_self_iff, Cycle, Cycle.coe_eq_coe, Cycle.Nodup, Cycle.Chain, List.next, List.prev, List.next_getElem, List.prev_getElem, List.next_prev, Cycle.next, Cycle.prev]
  E2: [List.rotate_mod, List.length_rotate, List.rotate_length, List.rotate_perm, List.nodup_rotate, List.rotate_cons_succ, List.rotate_append_length_eq, List.rotate_injective, List.rotate_eq_rotate, List.reverse_rotate, List.zipWith_rotate_distrib, List.rotate_eq_self_iff_eq_replicate, List.Nodup.rotate_congr, List.isRotated_iff_mod, List.isRotated_iff_mem_map_range, List.IsRotated.perm, List.IsRotated.nodup_iff, List.IsRotated.setoid, List.isRotated_reverse_iff, List.length_cyclicPermutations_of_ne_nil, List.cyclicPermutations_rotate, List.Nodup.cyclicPermutations, List.nextOr, List.prev_next, List.isRotated_next_eq, List.pmap_next_eq_rotate_one, Cycle.mk_eq_coe, Cycle.length, Cycle.nodup_coe_iff, Cycle.Nontrivial, Cycle.nontrivial_coe_nodup_iff, Cycle.Subsingleton, Cycle.reverse, Cycle.lists, Cycle.toMultiset, Cycle.chain_coe_cons, Cycle.chain_iff_pairwise, Cycle.forall_eq_of_chain, Cycle.chain_range_succ, Cycle.next_mem, Cycle.next_prev, Cycle.fintypeNodupCycle]
  E1: auto
families: []
requires: [V03.C02, V03.C04, V05.C07, V33.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Rotations and cycles

### Overview

Put the entries of a list on a circle. Then the list $[1, 2, 3]$ and its rotations $[2, 3, 1]$ and $[3, 1, 2]$ describe the same arrangement: only the starting point differs. Mathlib calls such an arrangement a cycle and defines the type `Cycle α` as the quotient of `List α` by the relation "is a rotation of". A cycle without repeated entries has a successor function `next` and a predecessor function `prev`, which are inverse permutations of its members. This is the bridge to the cyclic permutations of group theory: a cycle $(a_1\, a_2\, \dots\, a_k)$ in the notation of permutations corresponds to the cycle of the list $[a_1, \dots, a_k]$ in this sense.

This section studies `rotate` and its arithmetic, the relation `IsRotated`, the list of all cyclic permutations of a list, the type `Cycle`, chains on cycles, and the functions `next` and `prev`, with their relation to the permutations of a finite type.

### Definitions

**Definition (Rotation).** `l.rotate n` moves the first $n \bmod |l|$ entries of $l$ to the end: it is `drop (n % |l|) l ++ take (n % |l|) l`. The definition is in Batteries; Mathlib proves the lemmas. A slower form `rotate'` moves one entry at a time and serves in proofs.

**Definition (Rotated lists).** $l \sim_r l'$ (`List.IsRotated`) means that `l.rotate n = l'` for some $n$.

**Definition (Cyclic permutations).** `cyclicPermutations l` is the list of the rotations `l.rotate 0, …, l.rotate (|l| - 1)` for $l \neq [\,]$, and $[[\,]]$ for $l = [\,]$. The source builds it as the list of the lists `tails l` $i$ `++ inits l` $i$, without the last one.

**Definition (Cycle).** `Cycle α` is the quotient of `List α` by $\sim_r$ (the setoid `IsRotated.setoid`). A list $l$ gives the cycle $\uparrow l$. Membership, the length, `Nodup`, the reverse, the multiset of members (`toMultiset`) and the multiset of the representing lists (`lists`) are defined on lists and pass to the quotient, since rotations do not change them up to rotation. A cycle is `Nontrivial` if it has two different members, and `Subsingleton` if its length is at most $1$.

**Definition (Chain on a cycle).** `Cycle.Chain r ↑(a :: l)` is `IsChain r (a :: (l ++ [a]))`: the relation holds between neighbours, and also between the last entry and the first. The empty cycle is a chain.

**Definition (Next and prev).** For $x \in l$, `l.next x` is the entry after the first occurrence of $x$, or the head of $l$ if this occurrence is the last entry. It is `nextOr l x (head)`, where `nextOr` walks along the list and returns the default value at the end. `l.prev x` is the entry before the first occurrence of $x$, or the last entry of $l$ if $x$ is the head. For a cycle $s$ without duplicates, `Cycle.next s` and `Cycle.prev s` are the same functions on any representing list.

### Theorems and proofs

**Theorem (Entries of a rotation).** Let $L = |l|$. Then $|l.\operatorname{rotate} n| = L$, $l.\operatorname{rotate} n = \operatorname{drop} n\, l \mathbin{+\!\!+} \operatorname{take} n\, l$ for $n \le L$, and $(l.\operatorname{rotate} n)_k = l_{(k + n) \bmod L}$ for $k < L$. Also $(l.\operatorname{rotate} n).\operatorname{rotate} m = l.\operatorname{rotate} (n + m)$.

*Proof.* For $n < L$, $n \bmod L = n$; for $n = L$, $n \bmod L = 0$, and `drop L l ++ take L l = [] ++ l = l` equals `drop 0 l ++ take 0 l`. This gives the form with drop and take. Its length is $(L - n) + n = L$. For the entries, take $n < L$ first. If $k < L - n$, the entry is in `drop n l`, and it is $l_{n + k}$; here $k + n < L$, so $(k + n) \bmod L = k + n$. If $L - n \le k < L$, the entry is in `take n l` at position $k - (L - n)$, so it is $l_{k + n - L}$; here $L \le k + n < 2L$, so $(k + n) \bmod L = k + n - L$. For a general $n$, `l.rotate n = l.rotate (n % L)` by the definition, and $(k + n \bmod L) \bmod L = (k + n) \bmod L$. For the composition, both lists have length $L$, and their entries at $k$ are $l_{((k + m) \bmod L + n) \bmod L} = l_{(k + m + n) \bmod L}$. Two lists of equal length with equal entries are equal. $\square$

So $l.\operatorname{rotate} L = l$ (`rotate_length`), `rotate n` is injective (`rotate_injective`), and `l.rotate n` is a permutation of $l$ (`rotate_perm`), since it is a rearrangement of `drop n l ++ take n l`.

**Theorem (Rotation is an equivalence relation).** $\sim_r$ is reflexive, symmetric and transitive.

*Proof.* Reflexivity: `l.rotate 0 = l`. Transitivity: if `l.rotate n = l'` and `l'.rotate m = l''`, then `l.rotate (n + m) = l''` by the composition rule. Symmetry: let `l.rotate n = l'` and $L = |l|$, and let $j = n \bmod L$. If $L = 0$, then $l = l' = [\,]$. Else $l = l.\operatorname{rotate}(j + (L - j)) = (l.\operatorname{rotate} j).\operatorname{rotate}(L - j)$, since $l.\operatorname{rotate} L = l$; and $l.\operatorname{rotate} j = l'$ by `rotate_mod`. So `l'.rotate (L - j) = l`. $\square$

The proof of symmetry also shows that $l \sim_r l'$ if and only if `l.rotate n = l'` for some $n \le |l|$ (`isRotated_iff_mod`). Since a rotation is a permutation, $l \sim_r l'$ implies $l \sim l'$, and so $|l| = |l'|$, the same members, and `Nodup l ↔ Nodup l'`.

**Theorem (Cyclic permutations).** $l' \in \operatorname{cyclicPermutations} l$ if and only if $l' \sim_r l$, and for $l \neq [\,]$ the list `cyclicPermutations l` has $|l|$ entries. If $l$ has no duplicates, then neither has `cyclicPermutations l`.

*Proof.* For $l = [\,]$, the only rotation of $[\,]$ is $[\,]$. For $l \neq [\,]$, with $L = |l|$, the entry $i$ of `tails l` is `drop i l`, and the entry $i$ of `inits l` is `take i l`. So the entry $i < L$ of the list is `drop i l ++ take i l = l.rotate i`, and there are $L$ entries, since the last entry ($i = L$) is removed. Now $l' \sim_r l$ means $l \sim_r l'$, that is `l.rotate n = l'` for some $n$, and with `rotate_mod`, for some $n < L$. For the last claim: if `l.rotate i = l.rotate j` with $i, j < L$, then the entries at position $0$ give $l_i = l_j$, and since $l$ has no duplicates, $i = j$. $\square$

**Proposition (Rotations that fix a list).** If $l$ has no duplicates, then `l.rotate n = l` if and only if $l = [\,]$ or $n \bmod |l| = 0$. For a nonempty type, `l.rotate n = l` holds for all $n$ if and only if $l$ is constant, that is, $l = \operatorname{replicate} |l|\, a$ for some $a$.

*Proof.* Suppose $l \neq [\,]$, $L = |l|$ and `l.rotate n = l`. The entry at $0$ gives $l_{n \bmod L} = l_0$, and since $l$ has no duplicates, $n \bmod L = 0$. Conversely, $n \bmod L = 0$ gives `l.rotate n = l.rotate 0 = l`. For the second claim, a constant list has $l_{(k + n) \bmod L} = a = l_k$. If `l.rotate 1 = l`, then $l_{k + 1} = l_k$ for each $k + 1 < L$, so all entries are equal to $l_0$. $\square$

**Theorem (Next and prev on a list without duplicates).** Let $l$ have no duplicates and $L = |l|$. For $i < L$, `l.next lᵢ = l[(i + 1) % L]` and `l.prev lᵢ = l[(i + (L - 1)) % L]`. So `next` and `prev` are inverse maps of the members of $l$, and `next` is invariant under rotation of $l$.

*Proof.* The formula for `next` is by induction on $l$, following `nextOr`. For $y :: z :: xs$ and $x = l_i$: if $i = 0$, then $x = y$ and the result is $z = l_1$. If $i > 0$, then $x \neq y$, because $l$ has no duplicates, and the result is `nextOr (z :: xs) x d` with the same default $d = l_0$. If $x$ is the last entry, the walk reaches the end and returns $d = l_0 = l_{L \bmod L}$. Otherwise the hypothesis on $z :: xs$ gives the entry after $x$. The formula for `prev` is similar. Then `next (prev lᵢ) = l[((i + L - 1) % L + 1) % L] = l[(i + L) % L] = lᵢ`, and in the same way `prev (next lᵢ) = lᵢ`. For the invariance, let $l' = l.\operatorname{rotate} n$ and $x = l'_k = l_{(k + n) \bmod L}$. Then `l'.next x = l'[(k + 1) % L] = l[(k + 1 + n) % L]`, which is the successor of $x$ in $l$. $\square$

So, for a cycle $s$ without duplicates, `Cycle.next s` and `Cycle.prev s` are well defined, and `Cycle.next_prev` says that they are inverse. A list $l$ without duplicates also gives `List.formPerm l`, the product of the transpositions $(l_0\, l_1)(l_1\, l_2) \cdots (l_{L-2}\, l_{L-1})$, a permutation of all of $\alpha$. It agrees with `next` on the members (`formPerm_apply_getElem`) and fixes the other elements. For a nontrivial cycle without duplicates, `Cycle.formPerm` is a cyclic permutation in the sense of group theory (`Cycle.isCycle_formPerm`), and `Equiv.Perm.toCycle` goes back.

**Proposition (Chains on cycles).** If $r$ is transitive, `Cycle.Chain r s` holds if and only if $r(a, b)$ for all members $a$ and $b$ of $s$. If $r$ is also antisymmetric, a chain on a cycle has at most one distinct member.

*Proof.* Let $s = \uparrow(a :: l)$. The chain is `IsChain r (a :: (l ++ [a]))`. By transitivity, a chain is pairwise, so $r(x, y)$ for each $x$ before $y$ in $a :: l \mathbin{+\!\!+} [a]$. Each member $x$ is before the last $a$, so $r(x, a)$, and $a$ is before each member $y$, so $r(a, y)$; transitivity gives $r(x, y)$. The converse is clear, since neighbours are members. If $r$ is antisymmetric, $r(x, y)$ and $r(y, x)$ give $x = y$. $\square$

So a cycle of numbers that increases at each step of a circle does not exist, except the cycles of one value: $1 \le 2 \le 3 \le 1$ forces $1 = 2 = 3$.

### Examples

**Example (The rotations of [1, 2, 3]).** `[1, 2, 3].rotate 1 = drop 1 ++ take 1 = [2, 3] ++ [1] = [2, 3, 1]`. `rotate 2` gives $[3] \mathbin{+\!\!+} [1, 2] = [3, 1, 2]$, `rotate 3` gives $[1, 2, 3]$, and `rotate 4 = rotate 1`, since $4 \bmod 3 = 1$. The formula by entries checks `([1, 2, 3].rotate 2)[1] = l[(1 + 2) % 3] = l[0] = 1`. For `cyclicPermutations`: `tails` is $[[1, 2, 3], [2, 3], [3], [\,]]$, `inits` is $[[\,], [1], [1, 2], [1, 2, 3]]$, the appends are $[1, 2, 3], [2, 3, 1], [3, 1, 2], [1, 2, 3]$, and the last one is removed. So `cyclicPermutations [1, 2, 3] = [[1, 2, 3], [2, 3, 1], [3, 1, 2]]`.

**Example (The cycle of [1, 2, 3]).** The three rotations give one cycle: $\uparrow[1, 2, 3] = \uparrow[2, 3, 1] = \uparrow[3, 1, 2]$. Its reverse is $\uparrow[3, 2, 1]$, with the rotations $[3, 2, 1]$, $[2, 1, 3]$, $[1, 3, 2]$; none is $[1, 2, 3]$, so the reverse is a different cycle. `next` sends $1 \mapsto 2$, $2 \mapsto 3$ and $3 \mapsto 1$, where the last step wraps to the head, and `prev` sends $1 \mapsto 3$. On $[2, 3, 1]$ the same values result. `formPerm [1, 2, 3]` is $(1\,2)(2\,3)$: it sends $1$ to $2$ ($(2\,3)$ fixes $1$), $2$ to $3$, and $3$ to $1$ ($(2\,3)$ sends $3$ to $2$, then $(1\,2)$ sends $2$ to $1$), which is `next`.

**Counterexample (Next on a list with duplicates).** For $l = [1, 2, 1, 3]$, `next` uses the first occurrence: `l.next 1 = 2`, `l.next 2 = 1`, and `l.next 3 = 1`, since $3$ is the last entry and the walk returns the head. Two members go to $1$ and none goes to $3$, so `next` is not a bijection of the members. The hypothesis `Nodup` in `next_prev` is necessary.

**Counterexample (Rotation without the hypothesis Nodup).** `[1, 1].rotate 1 = [1, 1]`, although $1 \bmod 2 \neq 0$, so `Nodup.rotate_eq_self_iff` needs `Nodup`. Also `cyclicPermutations [1, 1] = [[1, 1], [1, 1]]` has duplicates.

```lean
example : [1, 2, 3].rotate 1 = [2, 3, 1] := rfl
example : [1, 2, 3].cyclicPermutations = [[1, 2, 3], [2, 3, 1], [3, 1, 2]] := rfl
example : [1, 2, 3].next 3 (by decide) = 1 := rfl
```

### The library around it

::: mathlib
`List.getElem_rotate` · `Mathlib.Data.List.Rotate`

`rotate_eq_drop_append_take`, `getElem_rotate`, `rotate_rotate`, `rotate_mod`, `length_rotate`, `rotate_length`, `rotate_perm`, `nodup_rotate`, `rotate_cons_succ`, `rotate_append_length_eq`, `rotate_injective`, `rotate_eq_rotate`, `reverse_rotate`, `zipWith_rotate_distrib`, `rotate_eq_self_iff_eq_replicate` and `Nodup.rotate_congr`.

<?decl List.getElem_rotate?>
:::

::: mathlib
`List.mem_cyclicPermutations_iff` · `Mathlib.Data.List.Rotate`

`IsRotated` (notation `~r`), `instIsEquivIsRotated`, `IsRotated.setoid`, `isRotated_iff_mod`, `isRotated_iff_mem_map_range`, `IsRotated.perm`, `IsRotated.nodup_iff`, `isRotated_reverse_iff`; `cyclicPermutations`, `mem_cyclicPermutations_iff`, `length_cyclicPermutations_of_ne_nil`, `cyclicPermutations_rotate` and `Nodup.cyclicPermutations`.

<?decl List.mem_cyclicPermutations_iff?>
:::

::: mathlib
`List.next_getElem` · `Mathlib.Data.List.Cycle`

`nextOr`, `next`, `prev`, `next_getElem`, `prev_getElem`, `next_prev`, `prev_next`, `isRotated_next_eq`, and `pmap_next_eq_rotate_one`: applying `next` to each entry of a list without duplicates gives `l.rotate 1`.

<?decl List.next_getElem?>
:::

::: mathlib
`Cycle.coe_eq_coe` · `Mathlib.Data.List.Cycle`

`Cycle`, `mk_eq_coe`, `coe_eq_coe`, `length`, `Nodup`, `nodup_coe_iff`, `Nontrivial`, `nontrivial_coe_nodup_iff`, `Subsingleton`, `reverse`, `lists`, `toMultiset`; `Chain`, `chain_coe_cons`, `chain_iff_pairwise`, `forall_eq_of_chain`, `chain_range_succ`; `next`, `prev`, `next_mem`, `next_prev`; and `fintypeNodupCycle`, the finite type of cycles without duplicates over a finite type.

<?decl Cycle.coe_eq_coe?>
:::

::: mathlib
`Cycle.isCycle_formPerm` · `Mathlib.GroupTheory.Perm.Cycle.Concrete`

`Cycle.formPerm`, `Cycle.isCycle_formPerm` and `Equiv.Perm.toCycle` connect the cycles of this section with the cyclic permutations of a finite type. `List.formPerm` and `List.formPerm_apply_getElem` are in `Mathlib.GroupTheory.Perm.List`.

<?decl Cycle.isCycle_formPerm?>
:::

Common errors of a learner: The first error is to confuse a cycle with a multiset; $\uparrow[1, 2, 3] \neq \uparrow[1, 3, 2]$, although the multisets of members agree. The second error is to rotate to the right; `rotate 1` moves the head to the end. The third error is to use `next` on a list with duplicates and to expect a bijection. The fourth error is to forget that `List.next` needs a proof of membership, so a term `l.next x h` carries the proof `h`.

### Exercises

1. (A) Compute `[a, b, c, d].rotate n` for $n = 1, 2, 5$, and `cyclicPermutations [a, b]`. Hint: $5 \bmod 4 = 1$.
2. (A) Decide whether $[1, 2, 3, 4] \sim_r [3, 4, 1, 2]$ and whether $[1, 2, 3, 4] \sim_r [2, 1, 4, 3]$. Hint: find $n$ with `rotate n` equal to the second list, or compare the successor of $1$.
3. (A) For $l = [5, 7, 9, 4]$, compute `next` and `prev` of each member, and check `next (prev x) = x`. Hint: the successor of $4$ is the head.
4. (B) Prove that `(l ++ l').rotate |l| = l' ++ l`. Hint: use `rotate_eq_drop_append_take` with $n = |l| \le |l \mathbin{+\!\!+} l'|$.
5. (B) Prove that $l \sim_r l'$ if and only if $\operatorname{rev}(l) \sim_r \operatorname{rev}(l')$. Hint: the reverse of `drop n l ++ take n l` is `rev (take n l) ++ rev (drop n l)`.
6. (B) Prove that a list $l$ without duplicates with $|l| = k \ge 1$ has exactly $k$ rotations, and deduce that the number of cycles without duplicates whose members are $k$ given elements is $(k - 1)!$. Hint: $k!$ orders of the elements, $k$ of them in each cycle.
7. (C) Let $l$ have no duplicates, $|l| = L \ge 2$. Prove that `formPerm l` sends $l_{L-1}$ to $l_0$, by a computation with the transpositions $(l_0\, l_1) \cdots (l_{L-2}\, l_{L-1})$. Hint: apply the factors from the right; each moves the value one place to the left.

### Notes and history

The cycle notation for permutations comes from the theory of substitutions of the nineteenth century, and it is the motivation for the type `Cycle`: the cycle $(1\,2\,3)$ of group theory is the class of the list $[1, 2, 3]$ under rotation. The number $(k - 1)!$ of cyclic orders of $k$ elements is classical; Knuth's *The Art of Computer Programming*, Volume 1, treats permutations in cycle form.

The Mathlib files are by these authors, read from their headers: `Rotate` by Chris Hughes and Yakov Pechersky; `Cycle` by Yakov Pechersky.

### Reference

<?reference?>
