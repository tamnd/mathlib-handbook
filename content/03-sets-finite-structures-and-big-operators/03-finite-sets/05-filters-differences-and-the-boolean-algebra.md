---
title: Filters, differences and the Boolean algebra of finsets
kind: api
modules:
  - Mathlib.Data.Finset.Basic
  - Mathlib.Data.Finset.Filter
  - Mathlib.Data.Finset.SDiff
  - Mathlib.Data.Finset.Disjoint
  - Mathlib.Data.Finset.BooleanAlgebra
  - Mathlib.Data.Finset.SymmDiff
  - Mathlib.Data.Finset.Range
  - Mathlib.Data.Finset.Pairwise
  - Mathlib.Data.Finset.CastCard
  - Mathlib.Data.Finset.Density
explains:
  E2: [Finset.filter_filter, Finset.filter_union_filter_not_eq, Finset.mem_sdiff, Finset.sdiff_union_of_subset, Finset.insert_erase, Finset.compl_union, Finset.mem_symmDiff, Finset.cast_card_union, Finset.dens_union_add_dens_inter]
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

## Filters, differences and the Boolean algebra of finsets

### Overview

The previous section gave the structure of a finset, the insert and the erase, and the lattice of union and intersection. This section continues with the operations that remove elements: the filter by a predicate, the difference $s \setminus t$ and the symmetric difference. It gives the disjointness of finsets and the disjoint union, the complement in a finite type, and the finset `Finset.range n` of the first $n$ natural numbers. It ends with two ways to count with values outside $\mathbb{N}$: the card cast to a ring with subtraction, and the density $|s| / |\alpha|$ of a finset in a finite type.

All these operations reduce to logic at one element, by their membership lemmas. The module `Mathlib.Data.Finset.Basic` is the place where the operations of the two sections meet: it holds the lemmas that mix insert, erase, filter, difference and disjointness. The counting rules of Section 3 and the sums of Chapter 6 split a finset with the lemmas of this section.

### The library around it

#### The filter

The module `Mathlib.Data.Finset.Filter` gives the lemmas for `Finset.filter p s`, the finset of the members of $s$ that satisfy $p$. Section 1 defined it, and its notation is `{x ∈ s | p x}`. The predicate needs an instance `DecidablePred p`, and no `DecidableEq α`, because the filter only drops entries of the multiset (`Finset.filter_val`). The membership lemma is `Finset.mem_filter`: $a \in \{x \in s \mid p(x)\} \iff a \in s \land p(a)$.

**Theorem (Two filters).** $\{x \in \{x \in s \mid p(x)\} \mid q(x)\} = \{x \in s \mid p(x) \land q(x)\}$. This is `Finset.filter_filter`.

*Proof sketch.* By `Finset.ext` and `Finset.mem_filter` twice, the claim is $(a \in s \land p(a)) \land q(a) \iff a \in s \land (p(a) \land q(a))$, the associativity of $\land$. $\square$

The other lemmas follow the same pattern. `Finset.filter_subset` gives $\{x \in s \mid p(x)\} \subseteq s$. `Finset.filter_true_of_mem` and `Finset.filter_eq_self` say that the filter is $s$ when each member satisfies $p$. `Finset.filter_eq_empty_iff` says that the filter is empty when no member does, and `Finset.filter_nonempty_iff` is the positive form. `Finset.filter_congr` replaces $p$ by a predicate $q$ that agrees with $p$ on $s$. `Finset.monotone_filter_right` says that a weaker predicate gives a larger filter. The coercion lemma is `Finset.coe_filter`.

The module `Mathlib.Data.Finset.Basic` relates the filter to the other operations.

| Lean name | Statement |
|---|---|
| `Finset.filter_union` | $\{x \in s_1 \cup s_2 \mid p\} = \{x \in s_1 \mid p\} \cup \{x \in s_2 \mid p\}$ |
| `Finset.filter_inter` | $\{x \in s \mid p\} \cap t = \{x \in s \cap t \mid p\}$ |
| `Finset.filter_or` | $\{x \in s \mid p \lor q\} = \{x \in s \mid p\} \cup \{x \in s \mid q\}$ |
| `Finset.filter_and` | $\{x \in s \mid p \land q\} = \{x \in s \mid p\} \cap \{x \in s \mid q\}$ |
| `Finset.filter_not` | $\{x \in s \mid \neg p\} = s \setminus \{x \in s \mid p\}$ |
| `Finset.filter_insert` | the filter of `insert a s` is `insert a` of the filter if $p(a)$, and the filter of $s$ if not |
| `Finset.filter_eq'` | $\{x \in s \mid x = b\}$ is $\{b\}$ if $b \in s$ and $\emptyset$ if not |
| `Finset.filter_ne'` | $\{x \in s \mid x \ne b\} = \operatorname{erase} s\, b$ |
| `Finset.filter_mem_eq_inter` | $\{x \in s \mid x \in t\} = s \cap t$ |
| `Finset.sdiff_eq_filter` | $s \setminus t = \{x \in s \mid x \notin t\}$ |

**Theorem (Splitting by a predicate).** $\{x \in s \mid p(x)\} \cup \{x \in s \mid \neg p(x)\} = s$, and the two parts are disjoint. These are `Finset.filter_union_filter_not_eq` and `Finset.disjoint_filter_filter_not`.

*Proof sketch.* For the union, the membership lemmas give $(a \in s \land p(a)) \lor (a \in s \land \neg p(a)) \iff a \in s$, by the excluded middle for $p(a)$. For the disjointness, an element of both parts satisfies $p(a)$ and $\neg p(a)$. $\square$

This split is the source of the rule `Finset.sum_filter_add_sum_filter_not` of Chapter 6 and of the card rule $|s| = |\{x \in s \mid p\}| + |\{x \in s \mid \neg p\}|$.

#### The difference

The module `Mathlib.Data.Finset.SDiff` defines the difference $s \setminus t$, with the instance `Finset.instSDiff`. It needs `DecidableEq α`.

**Theorem (Membership in a difference).** $a \in s \setminus t \iff a \in s \land a \notin t$. This is `Finset.mem_sdiff`.

The instance `Finset.instGeneralizedBooleanAlgebra` says that `Finset α` is a generalized Boolean algebra: a distributive lattice with a bottom element and a relative complement $s \setminus t$. So the general lemmas on `sdiff` of the order library apply to finsets, and the module restates the common ones with the names of finsets.

**Theorem (Difference and union).** If $s_1 \subseteq s_2$, then $(s_2 \setminus s_1) \cup s_1 = s_2$. This is `Finset.sdiff_union_of_subset`.

*Proof sketch.* By extensionality, the claim is $(a \in s_2 \land a \notin s_1) \lor a \in s_1 \iff a \in s_2$. From left to right, the first case gives $a \in s_2$, and the second case gives $a \in s_2$ by $s_1 \subseteq s_2$. From right to left, use the excluded middle for $a \in s_1$. $\square$

The table lists other rules of the module.

| Lean name | Statement |
|---|---|
| `Finset.sdiff_subset` | $s \setminus t \subseteq s$ |
| `Finset.sdiff_eq_empty_iff_subset` | $s \setminus t = \emptyset \iff s \subseteq t$ |
| `Finset.sdiff_eq_self_iff_disjoint` | $s \setminus t = s \iff s, t$ disjoint |
| `Finset.sdiff_union_self_eq_union` | $(s \setminus t) \cup t = s \cup t$ |
| `Finset.sdiff_union_inter` | $(s \setminus t) \cup (s \cap t) = s$ |
| `Finset.union_sdiff_distrib` | $(s_1 \cup s_2) \setminus t = (s_1 \setminus t) \cup (s_2 \setminus t)$ |
| `Finset.sdiff_sdiff_eq_self` | $t \subseteq s \to s \setminus (s \setminus t) = t$ |
| `Finset.sdiff_ssubset` | $t \subseteq s$ and $t$ nonempty imply $s \setminus t \subset s$ |
| `Finset.insert_sdiff_of_mem` | $x \in t \to (\operatorname{insert} x\, s) \setminus t = s \setminus t$ |

The erase is a special difference: `Finset.erase_eq` and `Finset.sdiff_singleton_eq_erase` give $\operatorname{erase} s\, a = s \setminus \{a\}$. The module `Mathlib.Data.Finset.Basic` holds the rules that mix insert and erase.

**Theorem (Insert after erase).** If $a \in s$, then $\operatorname{insert} a (\operatorname{erase} s\, a) = s$. This is `Finset.insert_erase`. Its twin `Finset.erase_insert` gives $\operatorname{erase} (\operatorname{insert} a\, s)\, a = s$ for $a \notin s$.

*Proof sketch.* By extensionality, the claim is $b = a \lor (b \ne a \land b \in s) \iff b \in s$. If $b = a$, both sides hold, because $a \in s$. If $b \ne a$, both sides say $b \in s$. $\square$

The rule `Finset.insert_erase` is the step of many proofs by induction that remove a chosen element $a \in s$ instead of the last inserted one. Its relatives are `Finset.erase_ssubset` ($\operatorname{erase} s\, a \subset s$ for $a \in s$), `Finset.subset_insert_iff` ($s \subseteq \operatorname{insert} a\, t \iff \operatorname{erase} s\, a \subseteq t$), `Finset.erase_union_distrib` and `Finset.union_erase_of_mem`.

#### Disjointness and the disjoint union

Two finsets are disjoint when their intersection is empty. Mathlib uses the predicate `Disjoint s t` of the order library, and the module `Mathlib.Data.Finset.Disjoint` turns it into statements about elements: `Finset.disjoint_left` ($a \in s \to a \notin t$), `Finset.disjoint_right`, `Finset.disjoint_iff_ne` and `Finset.not_disjoint_iff` ($\exists a \in s, a \in t$). The rules for the operations are `Finset.disjoint_singleton_left` ($\{a\}$ and $s$ are disjoint iff $a \notin s$), `Finset.disjoint_insert_left` and, in `Mathlib.Data.Finset.Basic`, `Finset.disjoint_union_left`, `Finset.disjoint_sdiff` and `Finset.disjoint_filter`. With `DecidableEq α`, disjointness is decidable (`Finset.decidableDisjoint`). The coercion lemmas are `Finset.disjoint_coe` and `Finset.disjoint_val`.

The function `Finset.disjUnion s t h` is the union of two disjoint finsets, with the proof `h : Disjoint s t` as an argument. Its multiset is the sum of the two multisets, so it needs no equality test. Membership is `Finset.mem_disjUnion`, and `Finset.disjUnion_eq_union` says that it equals $s \cup t$ when `DecidableEq α` is present. The equivalence `Equiv.Finset.union` identifies the subtype of $s \cup t$ with the sum type of the two subtypes for disjoint $s$ and $t$. Section 3 counts a disjoint union with this equivalence.

The module `Mathlib.Data.Finset.Pairwise` treats families of finsets. A family $f$ is pairwise disjoint on a set $s$ of indices when $f(i)$ and $f(j)$ are disjoint for $i \ne j$ in $s$. The lemma `Set.PairwiseDisjoint.elim_finset` gives the useful form: if $a \in f(i)$ and $a \in f(j)$, then $i = j$. The lemma `Finset.pairwiseDisjoint_coe` moves the property between finsets and sets, and `List.pairwise_iff_coe_toFinset_pairwise` relates a pairwise property of a list with no repetition to the same property of its finset.

#### The complement in a finite type

When $\alpha$ is a finite type, Chapter 4 gives the finset `Finset.univ` of all its elements. The module `Mathlib.Data.Finset.BooleanAlgebra` then makes `Finset α` a Boolean algebra (`Finset.booleanAlgebra`), with top element `Finset.univ` (`Finset.top_eq_univ`) and the complement $s^c$. The membership rule is `Finset.mem_compl`: $a \in s^c \iff a \notin s$. The complement is a difference: `Finset.compl_eq_univ_sdiff` gives $s^c = \mathrm{univ} \setminus s$, and `Finset.sdiff_eq_inter_compl` gives $s \setminus t = s \cap t^c$.

**Theorem (De Morgan).** $(s \cup t)^c = s^c \cap t^c$ and $(s \cap t)^c = s^c \cup t^c$. These are `Finset.compl_union` and `Finset.compl_inter`.

*Proof sketch.* By `Finset.mem_compl`, `Finset.mem_union` and `Finset.mem_inter`, the first claim is $\neg(p \lor q) \iff \neg p \land \neg q$, and the second is $\neg(p \land q) \iff \neg p \lor \neg q$. These are the laws of De Morgan in logic. $\square$

The other rules compute the complement of the standard finsets: `Finset.compl_singleton` gives $\{a\}^c = \operatorname{erase} \mathrm{univ}\, a$, and `Finset.compl_insert` gives $(\operatorname{insert} a\, s)^c = \operatorname{erase} s^c\, a$. `Finset.inter_compl` gives $s \cap s^c = \emptyset$, `Finset.univ_inter` gives $\mathrm{univ} \cap s = s$, and `Finset.subset_compl_iff_disjoint_right` gives $s \subseteq t^c \iff s, t$ disjoint. The coercion of $s^c$ is the complement of the set (`Finset.coe_compl`).

#### The symmetric difference

The module `Mathlib.Data.Finset.SymmDiff` treats $s \mathbin{\triangle} t = (s \setminus t) \cup (t \setminus s)$, the operation `symmDiff` of the order library, with `Finset.symmDiff_def`.

**Theorem (Membership in a symmetric difference).** $a \in s \mathbin{\triangle} t \iff (a \in s \land a \notin t) \lor (a \in t \land a \notin s)$. This is `Finset.mem_symmDiff`, and it follows from `Finset.symmDiff_def` with `Finset.mem_union` and `Finset.mem_sdiff`.

The symmetric difference detects equality: `Finset.symmDiff_eq_empty` gives $s \mathbin{\triangle} t = \emptyset \iff s = t$, and `Finset.symmDiff_nonempty` is the positive form. For disjoint finsets it is the union (`Finset.symmDiff_eq_union`). An injective map keeps it (`Finset.image_symmDiff`).

#### The finsets range n

The module `Mathlib.Data.Finset.Range` defines `Finset.range n`, the finset $\{0, 1, \ldots, n - 1\}$ of $\mathbb{N}$. Its multiset is `Multiset.range n` (`Finset.range_val`), and its coercion is the set `Set.Iio n` (`Finset.coe_range`). The membership rule is `Finset.mem_range`: $m \in \operatorname{range} n \iff m < n$. The recursion rules are `Finset.range_zero` ($\operatorname{range} 0 = \emptyset$), `Finset.range_one` and `Finset.range_add_one`: $\operatorname{range}(n + 1) = \operatorname{insert} n (\operatorname{range} n)$, with $n \notin \operatorname{range} n$ by `Finset.notMem_range_self`. These two facts give the rule of one more term for a sum over a range in Chapter 6. The order rules are `Finset.range_subset_range` ($\operatorname{range} n \subseteq \operatorname{range} m \iff n \le m$) and `Finset.range_mono`. The equivalence `notMemRangeEquiv k` identifies the numbers outside $\operatorname{range} k$ with $\mathbb{N}$, by $n \mapsto n - k$.

#### The card in a ring

The card is a natural number, and the subtraction of $\mathbb{N}$ truncates. The module `Mathlib.Data.Finset.CastCard` states the rules with a subtraction after a cast to a ring $R$ with `AddGroupWithOne R`, where the subtraction is exact.

**Theorem (Inclusion and exclusion in a ring).** In $R$, $|s \cup t| = |s| + |t| - |s \cap t|$. This is `Finset.cast_card_union`.

*Proof sketch.* Section 1 proved $|s \cup t| + |s \cap t| = |s| + |t|$ in $\mathbb{N}$. The cast to $R$ keeps the addition, so the same equation holds in $R$. Subtract $|s \cap t|$ on both sides, which is exact in a group. $\square$

The other rules of the module are `Finset.cast_card_inter`, `Finset.cast_card_sdiff` ($|t \setminus s| = |t| - |s|$ for $s \subseteq t$) and `Finset.cast_card_erase_of_mem` ($|\operatorname{erase} s\, a| = |s| - 1$ for $a \in s$).

#### The density of a finset

The module `Mathlib.Data.Finset.Density` defines `Finset.dens s` for a finset $s$ of a finite type $\alpha$. It is the nonnegative rational $|s| / |\alpha|$ (`Finset.dens_eq_card_div_card`), and `Finset.card_mul_dens` gives the form $|\alpha| \cdot \operatorname{dens} s = |s|$ with no division. The density is a probability: `Finset.dens_empty`, `Finset.dens_univ` (for a nonempty $\alpha$), `Finset.dens_le_one`, and `Finset.dens_eq_zero` ($\operatorname{dens} s = 0 \iff s = \emptyset$). It is monotone (`Finset.dens_mono`, `Finset.dens_le_dens`) and strictly monotone (`Finset.dens_lt_dens`).

**Theorem (Inclusion and exclusion for the density).** $\operatorname{dens}(s \cup t) + \operatorname{dens}(s \cap t) = \operatorname{dens} s + \operatorname{dens} t$. This is `Finset.dens_union_add_dens_inter`.

*Proof sketch.* Divide the identity $|s \cup t| + |s \cap t| = |s| + |t|$ of Section 1 by $|\alpha|$. If $\alpha$ is empty, all four densities are $0$, because each finset is empty. $\square$

The module follows the card API with `dens` for `card`: `Finset.dens_union_of_disjoint`, `Finset.dens_sdiff_add_dens`, `Finset.dens_filter_add_dens_filter_not_eq_dens` and `Finset.dens_image` for a bijection.

#### Common errors

1. To write `s \ t` and then fight the truncated subtraction of cards. Use `Finset.card_sdiff_add_card_inter` in $\mathbb{N}$, or `Finset.cast_card_sdiff` after a cast to $\mathbb{Z}$.
2. To use the complement $s^c$ in a type with no `Fintype` instance. In an infinite type the complement of a finset is not finite, so there is no complement of finsets. Use the difference $t \setminus s$ inside a fixed finset $t$, or pass to sets.
3. To expect `simp` to close a goal about `Finset.filter` with an instance of `DecidablePred` that differs from the one in the goal. The lemma `Finset.filter_congr_decidable` changes the instance, and `classical` at the start of the proof avoids the clash.

### Exercises

1. (A) Compute $\{x \in \operatorname{range} 10 \mid x \bmod 3 = 0\}$ and $\operatorname{range} 10 \setminus \operatorname{range} 4$, and give the card of each.
2. (A) Prove $s \setminus (t \cup u) = (s \setminus t) \cap (s \setminus u)$ with `Finset.ext` and the membership lemmas.
3. (A) In the type `Fin 6`, compute $\operatorname{dens}\{0, 2, 4\}$ and $\operatorname{dens}(\{0, 2, 4\}^c)$, and check that they add to $1$.
4. (B) Prove $(s \mathbin{\triangle} t) \mathbin{\triangle} u = s \mathbin{\triangle} (t \mathbin{\triangle} u)$ for finsets. Hint: an element is in $s \mathbin{\triangle} t$ iff exactly one of $a \in s$, $a \in t$ holds, so it is a sum modulo 2.
5. (B) Prove $|s \setminus t| = |s| - |s \cap t|$ in $\mathbb{Z}$ for all finsets $s, t$, with no hypothesis $t \subseteq s$. Hint: $s \setminus t = s \setminus (s \cap t)$.
6. (B) Let $f : \iota \to$ `Finset α` be pairwise disjoint on a finset $I$. Prove that the map that sends each $a$ in the union of the $f(i)$ to the unique $i \in I$ with $a \in f(i)$ is well defined, with `Set.PairwiseDisjoint.elim_finset`.

### Reference

<?reference?>
