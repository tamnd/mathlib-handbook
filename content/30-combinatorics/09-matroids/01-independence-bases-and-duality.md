---
title: "Matroids: independence, bases and duality"
kind: api
modules:
  - Mathlib.Combinatorics.Matroid.Init
  - Mathlib.Combinatorics.Matroid.Basic
  - Mathlib.Combinatorics.Matroid.IndepAxioms
  - Mathlib.Combinatorics.Matroid.Dual
  - Mathlib.Combinatorics.Matroid.Constructions
  - Mathlib.Combinatorics.Matroid.Sum
explains:
  E2: [Matroid.IsBase.exchange, Matroid.IsBase.encard_eq_encard_of_isBase, Matroid.Indep.exists_insert_of_not_isBase, IndepMatroid.matroid_indep_iff, Matroid.dual_isBase_iff, Matroid.dual_dual, Matroid.freeOn_dual_eq, Matroid.sigma_indep_iff, Matroid.disjointSum_indep_iff]
  E1: auto
families: []
requires: [V03.C01, V03.C05, V04.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Matroids: independence, bases and duality

### Overview

A finite matroid is a finite set $E$ with a nonempty family of *bases* $B \subseteq E$ such that for two bases $B_1, B_2$ and $e \in B_1 \setminus B_2$ there is $y \in B_2 \setminus B_1$ with $(B_1 \setminus \{e\}) \cup \{y\}$ a base. A set is *independent* if it is a subset of a base. The bases of a vector space and the spanning forests of a graph are the first examples.

Mathlib uses one definition for finite and infinite matroids. A term `M : Matroid α` has a ground set `M.E : Set α`, a predicate `M.IsBase` and a predicate `M.Indep`. The exchange property of the bases is an axiom, and a second axiom asks for maximal independent subsets of every subset of the ground set. For a finite ground set the second axiom is automatic, and the definition is the usual one. This section gives the axioms, the constructions from independence axioms, the dual matroid, the simple examples and the direct sums.

### The library around it

#### The structure `Matroid`

The module `Mathlib.Combinatorics.Matroid.Basic` defines `Matroid α` as a structure with these fields:

1. `E : Set α`, the ground set;
2. `IsBase : Set α → Prop` and `Indep : Set α → Prop`;
3. `indep_iff'`: a set is independent if and only if it is a subset of a base;
4. `exists_isBase`: there is a base;
5. `isBase_exchange`: the bases satisfy `Matroid.ExchangeProperty`;
6. `maximality`: for $X \subseteq E$, the independent subsets of $X$ satisfy `Matroid.ExistsMaximalSubsetProperty`, so each independent subset of $X$ is in a maximal independent subset of $X$;
7. `subset_ground`: each base is a subset of $E$.

A set is dependent, `M.Dep D`, if it is a subset of $E$ and not independent. A *basis* of $X$, `M.IsBasis I X`, is a maximal independent subset of $X$ with $X \subseteq E$. The variant `M.IsBasis' I X` has no condition on $X$. The module `Mathlib.Combinatorics.Matroid.Init` has no declarations. It declares the rule set of the tactic `aesop_mat`, which proves goals of the form `X ⊆ M.E` from the hypotheses.

| Lean name | Statement |
| --- | --- |
| `Matroid.indep_iff` | `M.Indep I ↔ ∃ B, M.IsBase B ∧ I ⊆ B` |
| `Matroid.isBase_iff_maximal_indep` | a base is a maximal independent set |
| `Matroid.Indep.subset` | a subset of an independent set is independent |
| `Matroid.IsBase.exchange` | for $e \in B_1 \setminus B_2$ there is $y \in B_2 \setminus B_1$ with `insert y (B₁ \ {e})` a base |
| `Matroid.IsBase.encard_eq_encard_of_isBase` | two bases have the same `encard` |
| `Matroid.Indep.exists_insert_of_not_isBase` | an independent set $I$ that is not a base has $e \in B \setminus I$ with `insert e I` independent, for each base $B$ |
| `Matroid.exists_isBasis` | each `X ⊆ M.E` has a basis |
| `Matroid.IsBasis.exists_isBase` | a basis of $X$ is `B ∩ X` for a base $B$ |
| `Matroid.ext_indep` | two matroids with the same ground set and the same independent subsets of it are equal |

The size of a base is the *rank* of the matroid. Mathlib measures it by `Set.encard` in $\mathbb{N}_\infty$, so two bases have the same size also when they are infinite. The typeclasses `M.Finite`, `M.RankFinite` and `M.RankInfinite` say that $E$ is finite, that a base is finite and that a base is infinite. The lemma `Matroid.rankFinite_or_rankInfinite` gives one of the two last classes. The class `M.Finitary` says that a set is independent if all its finite subsets are, and `Matroid.indep_iff_forall_finite_subset_indep` states this under `[M.Finitary]`.

**Theorem.** If $B_1$ and $B_2$ are bases of $M$ and $B_1 \subseteq B_2$, then $B_1 = B_2$.

*Proof.* By `Matroid.isBase_iff_maximal_indep`, the set $B_1$ is a maximal independent set. The set $B_2$ is independent and contains $B_1$, so maximality gives $B_2 \subseteq B_1$. $\square$

#### Matroids from independence axioms

To check the axioms of bases is often difficult. The module `Mathlib.Combinatorics.Matroid.IndepAxioms` defines the structure `IndepMatroid α` with these fields: a ground set, a predicate `Indep`, the empty set is independent, subsets of independent sets are independent, an augmentation axiom, a maximality axiom and `subset_ground`. The augmentation axiom says: if $I$ is independent and not maximal and $B$ is a maximal independent set, then there is $x \in B \setminus I$ with $I \cup \{x\}$ independent. The term `IndepMatroid.matroid` turns an `IndepMatroid` into a `Matroid`, and `IndepMatroid.matroid_indep_iff` says that the independent sets do not change.

Simpler sets of axioms give an `IndepMatroid`:

| Lean name | Hypotheses |
| --- | --- |
| `IndepMatroid.ofFinite` | finite ground set, the usual augmentation by `ncard` |
| `IndepMatroid.ofFinset` | the axioms for finite independent sets only, stated with `Finset` |
| `IndepMatroid.ofFinitary` | a set is independent if its finite subsets are; maximality follows by Zorn's lemma |
| `IndepMatroid.ofFinitaryCardAugment` | finitary, with augmentation by size for finite sets |
| `IndepMatroid.ofBdd` | the sizes of independent sets have an upper bound |
| `IndepMatroid.ofBddAugment` | bounded sizes, with augmentation by `encard` |

The constructions `Matroid.ofBase`, `Matroid.ofExistsFiniteIsBase` and `Matroid.ofIsBaseOfFinite` start from a predicate of bases instead.

#### The dual matroid

The module `Mathlib.Combinatorics.Matroid.Dual` defines `Matroid.dual M`, with the postfix notation `M✶`. Its ground set is `M.E`, and a set $I$ is independent in `M✶` if $I \subseteq E$ and $I$ is disjoint from some base of $M$. The construction goes through `Matroid.dualIndepMatroid`. The independent sets of `M✶` are the *coindependent* sets of $M$, `M.Coindep I`.

| Lean name | Statement |
| --- | --- |
| `Matroid.dual_ground` | `M✶.E = M.E` |
| `Matroid.dual_indep_iff_exists` | `M✶.Indep I ↔ ∃ B, M.IsBase B ∧ Disjoint I B`, for `I ⊆ M.E` |
| `Matroid.dual_isBase_iff` | `M✶.IsBase B ↔ M.IsBase (M.E \ B)`, for `B ⊆ M.E` |
| `Matroid.IsBase.compl_isBase_dual` | `M.IsBase B → M✶.IsBase (M.E \ B)` |
| `Matroid.dual_dual` | `M✶✶ = M` |
| `Matroid.coindep_iff_exists` | `M.Coindep X ↔ ∃ B, M.IsBase B ∧ B ⊆ M.E \ X` |

In the names of the library, `compl` means the difference with `M.E` and not the complement in `α`.

**Theorem.** $M^{**} = M$.

*Proof.* The two matroids have the ground set $E$, and by `Matroid.ext_isBase` it is sufficient to compare the bases $B \subseteq E$. By `Matroid.dual_isBase_iff` twice, $B$ is a base of $M^{**}$ if and only if $E \setminus B$ is a base of $M^*$, if and only if $E \setminus (E \setminus B) = B$ is a base of $M$. $\square$

#### Free, loopy and unique base matroids

The module `Mathlib.Combinatorics.Matroid.Constructions` defines four small matroids. The matroid `Matroid.emptyOn α` has the empty ground set. The matroid `Matroid.loopyOn E` has the ground set $E$ and the empty set as its only base. The matroid `Matroid.freeOn E` has $E$ as its only base and is defined as `(loopyOn E)✶`. The matroid `Matroid.uniqueBaseOn I E` has the ground set $E$ and the only base $I \cap E$.

| Lean name | Statement |
| --- | --- |
| `Matroid.loopyOn_indep_iff` | `(loopyOn E).Indep I ↔ I = ∅` |
| `Matroid.freeOn_indep_iff` | `(freeOn E).Indep I ↔ I ⊆ E` |
| `Matroid.freeOn_dual_eq` | `(freeOn E)✶ = loopyOn E` |
| `Matroid.loopyOn_dual_eq` | `(loopyOn E)✶ = freeOn E` |
| `Matroid.uniqueBaseOn_isBase_iff` | for `I ⊆ E`, the only base is $I$ |
| `Matroid.empty_isBase_iff` | `M.IsBase ∅ ↔ M = loopyOn M.E` |
| `Matroid.ground_indep_iff_eq_freeOn` | `M.Indep M.E ↔ M = freeOn M.E` |

#### Direct sums

The module `Mathlib.Combinatorics.Matroid.Sum` builds one direct construction, `Matroid.sigma`. For a family `M : (i : ι) → Matroid (α i)` it is a matroid on the sigma type, and a set is independent if each of its fibres is independent. The other sums come from `Matroid.sigma` and `Matroid.map`: `Matroid.sum'` on `ι × α`, `Matroid.disjointSigma` for a family on one type with pairwise disjoint ground sets, `Matroid.sum` on `α ⊕ β` and `Matroid.disjointSum` for two matroids on one type with disjoint ground sets.

| Lean name | Statement |
| --- | --- |
| `Matroid.sigma_indep_iff` | `(Matroid.sigma M).Indep I ↔ ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I)` |
| `Matroid.sigma_isBase_iff` | the same statement for bases |
| `Matroid.sum_indep_iff` | `(M.sum N).Indep I ↔ M.Indep (Sum.inl ⁻¹' I) ∧ N.Indep (Sum.inr ⁻¹' I)` |
| `Matroid.disjointSum_indep_iff` | $I$ is independent if `I ∩ M.E` and `I ∩ N.E` are independent and `I ⊆ M.E ∪ N.E` |
| `Matroid.disjointSum_comm` | the disjoint sum is commutative |

#### Common errors

1. A learner forgets the hypothesis `X ⊆ M.E`. Many lemmas, for example `Matroid.dual_isBase_iff`, take it as an argument with a default value. If `aesop_mat` cannot prove it, give the proof explicitly, often from `Matroid.Indep.subset_ground` or `Matroid.IsBase.subset_ground`.
2. A learner uses `Set.ncard` for the size of a base. The value of `ncard` on an infinite set is $0$, so a statement with `ncard` can be true for a bad reason. Use `Set.encard`, as in `Matroid.IsBase.encard_eq_encard_of_isBase`, or add `[M.RankFinite]`.
3. A learner writes `M*` for the dual. The notation is the postfix symbol `✶`, which is not the asterisk.

### Exercises

1. (A) Prove that each independent set of `loopyOn E` is empty and that `∅` is its only base, from `Matroid.loopyOn_indep_iff`.
2. (A) Prove that a subset of $E$ is coindependent in `freeOn E` if and only if it is empty, from `Matroid.freeOn_dual_eq`.
3. (B) Prove that two bases of a matroid of finite rank have the same `ncard`, from `Matroid.IsBase.encard_eq_encard_of_isBase`.
4. (B) Let $E$ be finite and let the independent sets be the subsets of $E$ with at most $r$ elements. Build this matroid with `IndepMatroid.ofFinite` and describe its dual.
5. (B) Prove that the bases of `M.disjointSum N h` are the sets $B_1 \cup B_2$ with $B_1$ a base of $M$ and $B_2$ a base of $N$.
6. (C) Prove `Matroid.Indep.exists_insert_of_not_isBase` from the exchange axiom and the maximality of bases.

### Reference

<?reference?>
