---
title: Rank functions of matroids
kind: api
modules:
  - Mathlib.Combinatorics.Matroid.Rank.Cardinal
  - Mathlib.Combinatorics.Matroid.Rank.ENat
  - Mathlib.Combinatorics.Matroid.Rank.Finite
explains:
  E2: [Matroid.eRk_inter_add_eRk_union_le, Matroid.IsBase.encard_eq_eRank, Matroid.eRank_add_eRank_dual, Matroid.IsCircuit.eRk_add_one_eq, Matroid.eRk_insert_eq_add_one, Matroid.eRk_closure_eq, Matroid.IsRkFinite.union, Matroid.IsBase.cardinalMk_eq, Matroid.toENat_cRank_eq, Matroid.invariantCardinalRank_of_finitary]
  E1: auto
families: []
requires: [V02.C08, V03.C05, V31.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Rank functions of matroids

### Overview

The rank of a matroid $M$ is the size of its bases, and the rank of a set $X$ is the size of the bases of $X$, that is the maximal independent subsets of $X$. For a finite matroid the rank function $r$ satisfies three rules. The first rule (R1) is $r(X) \leq |X|$. The second rule (R2) is $r(X) \leq r(Y)$ for $X \subseteq Y$. The third rule (R3) is submodularity, $r(X \cap Y) + r(X \cup Y) \leq r(X) + r(Y)$. On a finite set, each function with these three rules is the rank function of exactly one matroid, so the rank gives one more set of axioms for matroids.

Mathlib has two rank functions. The main one is `M.eRk X : ℕ∞`, with the rank `M.eRank : ℕ∞` of the matroid. Its value is the `Set.encard` of a basis, so all infinite sets have the value $\top$. All bases of a set have the same `encard`, with no hypothesis, and the full API of the rank works for each matroid. The second one is `M.cRk X : Cardinal`, with `M.cRank : Cardinal`. It sees the difference between infinite cardinals, but its good properties need the class `Matroid.InvariantCardinalRank`. The module docstring of `Mathlib.Combinatorics.Matroid.Basic` says that the equicardinality of bases in a general matroid is independent of ZFC, so the class is not a theorem for all matroids. The third module gives the predicate `M.IsRkFinite X` for the sets of finite rank.

The section uses the bases, the bases of a set and the duality of Section 1, the circuits and the closure of Section 2, and the restriction of Section 3. The numbers `ℕ∞` are in Volume 2, `Set.encard` is in Volume 3 and the cardinals are in Volume 31.

### The library around it

#### The rank and the rank of a set

The definitions are suprema, so that they make sense before any theorem about bases. The rank is `M.eRank = ⨆ B, B.encard` over the bases $B$, and the rank of a set is the rank of the restriction, `M.eRk X = (M ↾ X).eRank`. The first lemmas say that the supremum is the value at each base and at each basis.

| Lean name | Statement |
| --- | --- |
| `Matroid.IsBase.encard_eq_eRank` | for a base $B$, `B.encard = M.eRank` |
| `Matroid.IsBasis.encard_eq_eRk` | for a basis $I$ of $X$, `I.encard = M.eRk X` |
| `Matroid.IsBasis.eRk_eq_encard` | the same fact in the other direction |
| `Matroid.Indep.eRk_eq_encard` | for an independent $I$, `M.eRk I = I.encard` |
| `Matroid.indep_iff_eRk_eq_encard_of_finite` | a finite set $I$ is independent if and only if `M.eRk I = I.encard` |
| `Matroid.eRk_ground` | `M.eRk M.E = M.eRank` |
| `Matroid.eRk_le_eRank` | `M.eRk X ≤ M.eRank` |
| `Matroid.Indep.encard_le_eRank` | an independent set has at most `M.eRank` elements |
| `Matroid.eRank_le_encard_ground` | `M.eRank ≤ M.E.encard` |
| `Matroid.eRk_inter_ground` | `M.eRk (X ∩ M.E) = M.eRk X` |
| `Matroid.restrict_eRk_eq` | for $X \subseteq R$, `(M ↾ R).eRk X = M.eRk X` |
| `Matroid.eRank_map` | a map does not change the rank |

The lemma `Matroid.eRk_inter_ground` shows a convention: `M.eRk X` is defined for each set $X$ of the type, and the elements outside $M.E$ do not count.

The finite test `Matroid.indep_iff_eRk_eq_encard_of_finite` needs its hypothesis. If $I$ is infinite and dependent, it can still have rank $\top = |I|$. For example, in the free matroid on $\mathbb{N}$ with one more element $e$ that is a loop, the set $\mathbb{N} \cup \{e\}$ is dependent and has the rank $\top$.

#### The three rules

| Lean name | Statement |
| --- | --- |
| `Matroid.eRk_le_encard` | (R1) `M.eRk X ≤ X.encard` |
| `Matroid.eRk_mono` | (R2) `Monotone M.eRk` |
| `Matroid.eRk_inter_add_eRk_union_le` | (R3) `M.eRk (X ∩ Y) + M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y` |
| `Matroid.eRk_union_le_eRk_add_eRk` | `M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y` |
| `Matroid.eRk_singleton_le` | `M.eRk {e} ≤ 1` |
| `Matroid.eRk_insert_le_add_one` | `M.eRk (insert e X) ≤ M.eRk X + 1` |

The name `Matroid.eRk_submod` is an alias of the submodularity lemma.

The proof of (R3) uses only bases and the counting identity `Set.encard_union_add_encard_inter`, which says $|A \cup B| + |A \cap B| = |A| + |B|$ in `ℕ∞`. Let $I$ be a basis of $X \cap Y$, and extend it to a basis $J$ of $X \cup Y$ with $I \subseteq J$. The set $J \cap X$ is an independent subset of $X$, so $|J \cap X| \leq r(X)$, and in the same way $|J \cap Y| \leq r(Y)$. The counting identity gives

$$|J \cap X| + |J \cap Y| = |J \cap (X \cup Y)| + |J \cap X \cap Y| = |J| + |J \cap X \cap Y| \geq |J| + |I|.$$

The right side is $r(X \cup Y) + r(X \cap Y)$, so (R3) follows. There is no subtraction in the proof, and this is the reason that it works in `ℕ∞`.

#### Closure, circuits and loops

The rank of a set does not change when the set is replaced by its closure, and an element outside the closure adds exactly $1$. A circuit is a minimal dependent set, so it has rank one less than its size. The loops are the elements of rank $0$.

| Lean name | Statement |
| --- | --- |
| `Matroid.eRk_closure_eq` | `M.eRk (M.closure X) = M.eRk X` |
| `Matroid.eRk_insert_eq_add_one` | for $e \in M.E \setminus \operatorname{cl}(X)$, `M.eRk (insert e X) = M.eRk X + 1` |
| `Matroid.eRk_eq_of_eRk_insert_le_forall` | for $X \subseteq Y$, if no element of $Y \setminus X$ increases the rank of $X$, then `M.eRk X = M.eRk Y` |
| `Matroid.IsCircuit.eRk_add_one_eq` | for a circuit $C$, `M.eRk C + 1 = C.encard` |
| `Matroid.IsLoop.eRk_eq` | for a loop $e$, `M.eRk {e} = 0` |
| `Matroid.eRk_eq_zero_iff` | for $X \subseteq M.E$, `M.eRk X = 0` if and only if $X$ is a set of loops |
| `Matroid.eRank_eq_zero_iff` | `M.eRank = 0` if and only if `M = loopyOn M.E` |

For the circuit lemma, take $e \in C$. The set $C \setminus \{e\}$ is independent, because $C$ is a minimal dependent set, and it is a basis of $C$, because $C$ is dependent. So $r(C) = |C \setminus \{e\}|$ and $r(C) + 1 = |C|$. The lemma has the form $r(C) + 1 = |C|$ and not $r(C) = |C| - 1$, because truncated subtraction in `ℕ∞` loses information when $C$ is infinite.

#### The rank of the dual

A base $B$ of $M$ has the complement $M.E \setminus B$ as a base of $M^*$. The two sets are disjoint with the union $M.E$, so the two ranks add up to the size of the ground set. For a set $X \subseteq M.E$, the same argument with a basis gives a formula without subtraction.

| Lean name | Statement |
| --- | --- |
| `Matroid.eRank_add_eRank_dual` | `M.eRank + M✶.eRank = M.E.encard` |
| `Matroid.eRk_dual_add_eRank` | for $X \subseteq M.E$, `M✶.eRk X + M.eRank = M.eRk (M.E \ X) + X.encard` |

For a finite matroid the second lemma is the usual formula $r^*(X) = |X| + r(E \setminus X) - r(E)$. For example, let $M$ be the matroid on four elements whose bases are the six sets of size $2$. Its dual has the complements as bases, which are again the six sets of size $2$, and $2 + 2 = 4$.

#### Sets of finite rank

The predicate `M.IsRkFinite X` is defined as `(M ↾ X).RankFinite`, so it says that the bases of $X$ are finite. It is the right condition for the arithmetic of `eRk` without $\top$, and it is closed under the usual operations.

| Lean name | Statement |
| --- | --- |
| `Matroid.eRk_lt_top_iff` | `M.eRk X < ⊤` if and only if `M.IsRkFinite X` |
| `Matroid.isRkFinite_iff` | for $X \subseteq M.E$, `M.IsRkFinite X` if and only if $X$ has a finite basis |
| `Matroid.isRkFinite_of_finite` | a finite set has finite rank |
| `Matroid.Indep.isRkFinite_iff_finite` | an independent set has finite rank if and only if it is finite |
| `Matroid.IsRkFinite.subset` | a subset of a set of finite rank has finite rank |
| `Matroid.IsRkFinite.union` | the union of two sets of finite rank has finite rank |
| `Matroid.IsRkFinite.closure` | the closure of a set of finite rank has finite rank |
| `Matroid.IsRkFinite.diff` | `M.IsRkFinite (X \ Y)` when `M.IsRkFinite X` |
| `Matroid.isRkFinite_ground_iff_rankFinite` | `M.IsRkFinite M.E` if and only if `M.RankFinite` |
| `Matroid.isRkFinite_set` | in a matroid of finite rank each set has finite rank |

For the union, take finite bases $I$ of $X$ and $J$ of $Y$. Then $X \cup Y$ is in the closure of the finite set $I \cup J$, and a finite set has finite rank. The closure lemma and the subset lemma give the result. A set of finite rank can be infinite: in a matroid with infinitely many loops, the set of loops has rank $0$.

#### Cardinal rank

The cardinal rank `M.cRank` is the supremum of the cardinals `#B` of the bases, and `M.cRk X = (M ↾ X).cRank`. These definitions need no hypothesis, but their good properties need the class `M.InvariantCardinalRank`. Its one field `forall_card_isBasis_diff` says that two bases $I$ and $J$ of the same set have $\#(I \setminus J) = \#(J \setminus I)$. From this the bases of each set have the same cardinal.

| Lean name | Statement |
| --- | --- |
| `Matroid.cRk_le_cardinalMk` | `M.cRk X ≤ #X` |
| `Matroid.Indep.cardinalMk_le_cRank` | an independent set has cardinal at most `M.cRank` |
| `Matroid.toENat_cRank_eq` | `Cardinal.toENat M.cRank = M.eRank` |
| `Matroid.toENat_cRk_eq` | `Cardinal.toENat (M.cRk X) = M.eRk X` |
| `Matroid.IsBasis.cardinalMk_sdiff_comm` | with the class, $\#(I \setminus J) = \#(J \setminus I)$ for two bases of $X$ |
| `Matroid.IsBasis.cardinalMk_eq` | with the class, two bases of $X$ have the same cardinal |
| `Matroid.IsBase.cardinalMk_eq` | with the class, two bases of $M$ have the same cardinal |
| `Matroid.IsBase.cardinalMk_eq_cRank` | with the class, `#B = M.cRank` for a base $B$ |
| `Matroid.cRk_inter_add_cRk_union_le` | with the class, `M.cRk` is submodular |
| `Matroid.invariantCardinalRank_of_finitary` | each finitary matroid has the class |

The class is closed under the operations of Section 3: there are instances for restrictions, maps and comaps, such as `Matroid.invariantCardinalRank_restrict` and `Matroid.invariantCardinalRank_map`. The instance `Matroid.invariantCardinalRank_of_finitary` covers the matroids of linear independence of vectors, where each dependent set has a finite dependent subset. The two `toENat` lemmas say that the `ℕ∞` rank is the cardinal rank after all the infinite cardinals are sent to $\top$. These two lemmas need no class, so the `ℕ∞` rank is the safe choice when the infinite values do not matter.

#### Common errors

1. Using `M.eRk X - 1` or another subtraction in `ℕ∞`. The value $\top - 1$ is $\top$, and the lemmas of the library avoid subtraction. Use the additive forms such as `Matroid.IsCircuit.eRk_add_one_eq` and `Matroid.eRk_dual_add_eRank`, or prove `M.IsRkFinite X` first.
2. Using `Matroid.IsBase.cardinalMk_eq` without the class `InvariantCardinalRank`. The class is found automatically only for finitary matroids and for the constructions with an instance. For other matroids, use `Matroid.IsBase.encard_eq_eRank`, which needs no class.
3. Forgetting the hypothesis $X \subseteq M.E$ of lemmas such as `Matroid.eRk_eq_zero_iff` and `Matroid.eRk_dual_add_eRank`. It is an `autoParam` proved by `aesop_mat`, and when this tactic fails the error is at the use of the lemma.

### Exercises

1. (A) Let $M$ be the matroid on $\{1, 2, 3\}$ whose bases are the three sets of size $2$. Compute `M.eRk X` for each of the eight subsets $X$, and check (R3) for $X = \{1, 2\}$ and $Y = \{2, 3\}$.
2. (A) Use `Matroid.eRank_add_eRank_dual` to compute the rank of the dual of the free matroid `freeOn E` and of the loopy matroid `loopyOn E` for a finite set $E$ with $n$ elements.
3. (B) Show that $r(X) + r(Y) \geq r(X \cup Y)$ from (R3) and the fact that a rank is at least $0$. Compare with `Matroid.eRk_union_le_eRk_add_eRk`.
4. (B) Prove that `M.eRk (insert e X) = M.eRk X` when $X \subseteq M.E$ and $e \in \operatorname{cl}(X)$. Use `Matroid.eRk_mono` and `Matroid.eRk_closure_eq`.
5. (B) Give a matroid and a set $X$ with `M.IsRkFinite X` and $X$ infinite. Explain why `Matroid.eRk_lt_top_iff` does not need $X$ to be finite.
6. (C) Let $I$ and $J$ be bases of the same set $X$ in a finitary matroid. Prove that `#I = #J` from `Matroid.IsBasis.cardinalMk_sdiff_comm` and the decomposition $I = (I \setminus J) \cup (I \cap J)$.

### Reference

<?reference?>
