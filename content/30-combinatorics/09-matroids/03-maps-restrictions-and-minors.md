---
title: Maps, restrictions and minors
kind: api
modules:
  - Mathlib.Combinatorics.Matroid.Map
  - Mathlib.Combinatorics.Matroid.Minor.Restrict
  - Mathlib.Combinatorics.Matroid.Minor.Delete
  - Mathlib.Combinatorics.Matroid.Minor.Contract
  - Mathlib.Combinatorics.Matroid.Minor.Order
explains:
  E2: [Matroid.map_dual, Matroid.comap_indep_iff, Matroid.restrict_indep_iff, Matroid.delete_indep_iff, Matroid.dual_delete, Matroid.IsBasis.contract_indep_iff, Matroid.contract_loops_eq, Matroid.contract_delete_comm, Matroid.IsMinor.exists_eq_contract_delete_disjoint, Matroid.IsMinor.trans]
  E1: auto
families: []
requires: [V03.C01, V04.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Maps, restrictions and minors

### Overview

This section gives the operations that make new matroids from old ones. A map moves a matroid along a function from one type to another. A restriction keeps the elements of a set $R$ and keeps the independent sets that are in $R$. A deletion removes a set $D$, and it is the restriction to $M.E \setminus D$. A contraction of a set $C$ is the dual operation: the contraction $M / C$ is the dual of the deletion $M^* \setminus C$. A minor of $M$ is a matroid that comes from $M$ by a contraction and then a deletion.

In Mathlib all these matroids have the same type `Matroid α` as the matroid $M$, except the maps, which change the type. The ground set of the result is a subset of the type, as in Section 1. The notations `M ↾ R`, `M ＼ D` and `M ／ C` are scoped, so they need `open Matroid`. The symbols `＼` and `／` are the full width backslash and slash, not the ASCII characters. The dual is `M✶`, and the minor relation is `N ≤m M`.

The facts about independent sets, bases and duality of Section 1 are used everywhere, and the closure and the loops of Section 2 give the description of the loops of a contraction. The partial orders come from Volume 4.

### The library around it

#### Maps and comaps

A function $f : \alpha \to \beta$ moves a matroid in two directions. The comap `N.comap f` pulls a matroid $N$ on $\beta$ back to $\alpha$. Its ground set is $f^{-1}(N.E)$, and a set $I$ is independent when $f$ is injective on $I$ and $f(I)$ is independent in $N$. Two elements with the same image are never independent together, so the comap can have parallel elements. The map `M.map f hf` pushes a matroid $M$ on $\alpha$ forward to $\beta$. It needs a proof `hf` that $f$ is injective on $M.E$, and its independent sets are the images of the independent sets of $M$.

| Lean name | Statement |
| --- | --- |
| `Matroid.comap_indep_iff` | $I$ is independent in `N.comap f` if and only if $f(I)$ is independent in $N$ and $f$ is injective on $I$ |
| `Matroid.comap_ground_eq` | the ground set of `N.comap f` is $f^{-1}(N.E)$ |
| `Matroid.map_indep_iff` | $I$ is independent in `M.map f hf` if and only if $I = f(I_0)$ for an independent $I_0$ of $M$ |
| `Matroid.map_ground` | the ground set of `M.map f hf` is $f(M.E)$ |
| `Matroid.map_isBase_iff` | the bases of the map are the images of the bases of $M$ |
| `Matroid.map_dual` | $(M.\mathrm{map}\, f)^* = M^*.\mathrm{map}\, f$ |
| `Matroid.map_comap` | when $N.E \subseteq \operatorname{range} f$ and $f$ is injective on $f^{-1}(N.E)$, the map of the comap is $N$ |
| `Matroid.map_id` | the map along `id` is $M$ |

The map commutes with the dual because an injective map on $M.E$ sends the complement $M.E \setminus B$ of a base to the complement $f(M.E) \setminus f(B)$ of the image base. The bases of $M^*$ are the complements of the bases of $M$, so both sides of `Matroid.map_dual` have the same bases.

There are three special forms of the map. The map `M.mapEmbedding f` along an embedding `f : α ↪ β` needs no injectivity proof, and `M.mapEquiv f` along an equivalence `f : α ≃ β` is an isomorphism of matroids. The matroid `M.restrictSubtype X` has the type `Matroid ↥X` and the ground set `univ`. It is the comap of `M ↾ X` along the coercion, and it moves a matroid to a type that is equal to its ground set.

| Lean name | Statement |
| --- | --- |
| `Matroid.mapEmbedding_indep_iff` | $I$ is independent in `M.mapEmbedding f` if and only if $f^{-1}(I)$ is independent and $I \subseteq \operatorname{range} f$ |
| `Matroid.mapEquiv_indep_iff` | $I$ is independent in `M.mapEquiv f` if and only if $f^{-1}(I)$ is independent in $M$ |
| `Matroid.restrictSubtype_indep_iff` | a set $I$ of `↥X` is independent if and only if its image in $\alpha$ is independent in $M$ |
| `Matroid.restrictSubtype_ground` | the ground set of `M.restrictSubtype X` is `univ` |
| `Matroid.restrictSubtype_dual` | the dual of `M.restrictSubtype M.E` is `M✶.restrictSubtype M.E` |

The function `Matroid.comapOn N E f` is the restriction of `N.comap f` to a set $E$. It makes, for example, a matroid on a set of indices from a matroid on a set of vectors.

#### Restriction

The restriction `M ↾ R` has the ground set $R$ and the independent sets of $M$ that are subsets of $R$. The set $R$ need not be a subset of $M.E$. An element of $R \setminus M.E$ is in no independent set of $M$, so it becomes a loop of `M ↾ R`. This rule makes `M ↾ R` a total function of $R$, with no side condition.

| Lean name | Statement |
| --- | --- |
| `Matroid.restrict_indep_iff` | $I$ is independent in `M ↾ R` if and only if $I$ is independent in $M$ and $I \subseteq R$ |
| `Matroid.restrict_ground_eq` | the ground set of `M ↾ R` is $R$ |
| `Matroid.isBase_restrict_iff` | for $X \subseteq M.E$, the bases of `M ↾ X` are the bases of $X$ in $M$ |
| `Matroid.IsBasis.restrict_isBase` | a basis $I$ of $X$ is a base of `M ↾ X` |
| `Matroid.restrict_ground_eq_self` | `M ↾ M.E = M` |
| `Matroid.restrict_restrict_eq` | for $R_2 \subseteq R_1$, `M ↾ R₁ ↾ R₂ = M ↾ R₂` |

The relation `N ≤r M`, that is `Matroid.IsRestriction N M`, says that $N = M ↾ R$ for a set $R \subseteq M.E$. It is a partial order, with `Matroid.IsRestriction.trans` and `Matroid.IsRestriction.antisymm`. Mathlib puts the instance of `PartialOrder` for this relation on the structure `Matroid.Matroidᵣ α`, a wrapper of `Matroid α` with one field `toMatroid`, because the order `≤` on `Matroid α` is the minor order. The lemma `Matroid.ofMatroid_le_iff` connects the two forms. For a finite matroid, `Matroid.finite_setOfPred_isRestriction` says that $M$ has only finitely many restrictions.

| Lean name | Statement |
| --- | --- |
| `Matroid.IsRestriction.indep_iff` | if `N ≤r M`, then $I$ is independent in $N$ if and only if it is independent in $M$ and $I \subseteq N.E$ |
| `Matroid.IsRestriction.of_subset` | for $R \subseteq R'$, `M ↾ R ≤r M ↾ R'` |
| `Matroid.restrict_isStrictRestriction` | for $R \subsetneq M.E$, `M ↾ R <r M` |
| `Matroid.IsBasis.encard_eq_encard` | two bases of the same set have the same `encard` |
| `Matroid.Indep.augment` | if $I, J$ are independent and $|I| < |J|$, then some $e \in J \setminus I$ gives an independent `insert e I` |

The last two lemmas are in the module of restrictions. They are the equicardinality of bases and the augmentation axiom in the `ℕ∞` form, and Section 4 uses them for the rank.

#### Deletion

The deletion `M ＼ D` is the restriction `M ↾ (M.E \ D)`. It is the definition, so `Matroid.delete_eq_restrict` is true by `rfl`. Unlike the restriction, a deletion never adds loops.

| Lean name | Statement |
| --- | --- |
| `Matroid.delete_indep_iff` | $I$ is independent in `M ＼ D` if and only if $I$ is independent in $M$ and disjoint from $D$ |
| `Matroid.delete_ground` | the ground set of `M ＼ D` is $M.E \setminus D$ |
| `Matroid.delete_isBase_iff` | $B$ is a base of `M ＼ D` if and only if $B$ is a basis of $M.E \setminus D$ in $M$ |
| `Matroid.delete_isBasis_iff` | $I$ is a basis of $X$ in `M ＼ D` if and only if it is a basis of $X$ in $M$ and $X$ is disjoint from $D$ |
| `Matroid.delete_delete` | `M ＼ D₁ ＼ D₂ = M ＼ (D₁ ∪ D₂)` |
| `Matroid.delete_empty` | `M ＼ ∅ = M` |
| `Matroid.delete_isRestriction` | `M ＼ D ≤r M` |

#### Contraction

The contraction is defined by duality: `M ／ C = (M✶ ＼ C)✶`. Its ground set is $M.E \setminus C$. The first lemmas give the duality in the two directions. The independent sets of a contraction are given by a basis $I$ of $C$: a set $J$ disjoint from $C$ is independent in $M / C$ when $J \cup I$ is independent in $M$. If $C$ is itself independent, it is its own basis.

| Lean name | Statement |
| --- | --- |
| `Matroid.dual_delete` | $(M \setminus X)^* = M^* / X$ |
| `Matroid.dual_contract` | $(M / X)^* = M^* \setminus X$ |
| `Matroid.contract_ground` | the ground set of `M ／ C` is $M.E \setminus C$ |
| `Matroid.Indep.contract_indep_iff` | for an independent $I$, $J$ is independent in `M ／ I` if and only if $J$ is disjoint from $I$ and $J \cup I$ is independent |
| `Matroid.IsBasis.contract_indep_iff` | for a basis $I$ of $X$, $J$ is independent in `M ／ X` if and only if $J \cup I$ is independent and $X$ is disjoint from $J$ |
| `Matroid.Indep.contract_isBase_iff` | for an independent $I$, $B$ is a base of `M ／ I` if and only if $B \cup I$ is a base and $B$ is disjoint from $I$ |
| `Matroid.IsBasis.contract_eq_contract_delete` | for a basis $I$ of $X$, `M ／ X = M ／ I ＼ (X \ I)` |
| `Matroid.contract_closure_eq` | the closure of $X$ in `M ／ C` is $\operatorname{cl}_M(X \cup C) \setminus C$ |
| `Matroid.contract_loops_eq` | the loops of `M ／ C` are $\operatorname{cl}_M(C) \setminus C$ |
| `Matroid.contract_isLoop_iff_mem_closure` | $e$ is a loop of `M ／ C` if and only if $e \in \operatorname{cl}_M(C)$ and $e \notin C$ |
| `Matroid.contract_contract` | `M ／ C₁ ／ C₂ = M ／ (C₁ ∪ C₂)` |
| `Matroid.contract_delete_comm` | for disjoint $C$ and $D$, `M ／ C ＼ D = M ＼ D ／ C` |
| `Matroid.contract_eq_delete_of_subset_loops` | if $X$ is a set of loops, then `M ／ X = M ＼ X` |
| `Matroid.contract_eq_delete_of_subset_coloops` | if $X$ is a set of coloops, then `M ／ X = M ＼ X` |

The description of the loops follows from the closure formula. The loops of a matroid are the closure of $\emptyset$, so the loops of $M / C$ are $\operatorname{cl}_M(\emptyset \cup C) \setminus C$. In a graph this is the familiar rule: when the edges of $C$ are contracted, an edge becomes a loop exactly when its two ends are joined by a path in $C$.

The lemma `Matroid.IsBasis.contract_eq_contract_delete` reduces a contraction to the contraction of an independent set. The elements of $X \setminus I$ are in the closure of $I$, so they are loops of $M / I$, and the contraction of loops is their deletion.

#### Minors

The relation `N ≤m M`, that is `Matroid.IsMinor N M`, says that $N = M / C \setminus D$ for some sets $C$ and $D$. This order of the operations is not a restriction, because `Matroid.contract_delete_comm` and the rules for repeated deletions and contractions put each mixed sequence of operations into this form. The relation is the partial order `≤` of the instance `PartialOrder (Matroid α)`, and `Matroid.le_eq_isMinor` says this.

| Lean name | Statement |
| --- | --- |
| `Matroid.contract_delete_isMinor` | `M ／ C ＼ D ≤m M` |
| `Matroid.IsMinor.exists_eq_contract_delete_disjoint` | if `N ≤m M`, then $N = M / C \setminus D$ with $C, D \subseteq M.E$ disjoint |
| `Matroid.IsMinor.refl` | `M ≤m M` |
| `Matroid.IsMinor.trans` | the minor relation is transitive |
| `Matroid.IsMinor.antisymm` | if `N ≤m M` and `M ≤m N`, then $N = M$ |
| `Matroid.IsMinor.subset` | if `N ≤m M`, then $N.E \subseteq M.E$ |
| `Matroid.isStrictMinor_iff_isMinor_ssubset` | `N <m M` if and only if `N ≤m M` and $N.E \subsetneq M.E$ |
| `Matroid.Indep.of_isMinor` | an independent set of a minor is independent in $M$ |
| `Matroid.IsLoop.of_isMinor` | a loop of $M$ in the ground set of a minor $N$ is a loop of $N$ |

The proof of transitivity shows the use of the normal form. Let $M_1 = M_2 / C_1 \setminus D_1$ and $M_2 = M_3 / C_2 \setminus D_2$, with $C_1$ and $D_2$ disjoint, which the disjoint form gives because $C_1 \subseteq M_2.E$. Then $M_1 = M_3 / C_2 \setminus D_2 / C_1 \setminus D_1 = M_3 / C_2 / C_1 \setminus D_2 \setminus D_1$ by `Matroid.contract_delete_comm`, and this is $M_3 / (C_2 \cup C_1) \setminus (D_2 \cup D_1)$.

#### Common errors

1. Writing `M \ D` with the ASCII backslash. This is the difference of sets, and it does not type check on matroids. The deletion is `M ＼ D` with the full width symbol, after `open Matroid`.
2. Expecting `M ↾ R` to have no loops outside $M$. The elements of $R \setminus M.E$ are loops of `M ↾ R`. Use `M ＼ D`, or prove $R \subseteq M.E$, when this is not the intent.
3. Writing `N ≤ M` and expecting the restriction order. On `Matroid α` the order `≤` is the minor order. The restriction order `≤r` has its `PartialOrder` only on `Matroid.Matroidᵣ α`.

### Exercises

1. (A) Use `Matroid.delete_indep_iff` and `Matroid.restrict_indep_iff` to show that the independent sets of `M ＼ D` and `M ↾ (M.E \ D)` are the same.
2. (A) Let $M$ be the free matroid on $\{1, 2, 3\}$ and let $C = \{1\}$. Find the independent sets of `M ／ C` with `Matroid.Indep.contract_indep_iff`, and show that `M ／ C = M ＼ C`.
3. (B) Show that an element $e \in R \setminus M.E$ is a loop of `M ↾ R`. Use only `Matroid.restrict_indep_iff` and the fact that independent sets of $M$ are subsets of $M.E$.
4. (B) Let $f : \alpha \to \beta$ be constant. Describe the independent sets of `N.comap f` for each matroid $N$ on $\beta$, in the three cases where the value $b$ of $f$ is a nonloop of $N$, a loop of $N$, or not in $N.E$.
5. (B) Prove that $(M / C)^{*} = M^{*} \setminus C$ from the definition `M ／ C = (M✶ ＼ C)✶` and `Matroid.dual_dual`.
6. (C) Prove that the minor relation is antisymmetric. Use `Matroid.IsMinor.subset` to get $N.E = M.E$, then show that $C$ and $D$ in the disjoint normal form are empty.

### Reference

<?reference?>
