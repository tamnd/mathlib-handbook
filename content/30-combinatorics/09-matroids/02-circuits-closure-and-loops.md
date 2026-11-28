---
title: Circuits, closure and loops
kind: api
modules:
  - Mathlib.Combinatorics.Matroid.Circuit
  - Mathlib.Combinatorics.Matroid.Closure
  - Mathlib.Combinatorics.Matroid.Loop
explains:
  E2: [Matroid.Indep.fundCircuit_isCircuit, Matroid.dep_iff_superset_isCircuit, Matroid.IsCircuit.strong_elimination, Matroid.finitary_iff_forall_isCircuit_finite, Matroid.IsBase.mem_fundCocircuit_iff_mem_fundCircuit, Matroid.IsCircuit.inter_isCocircuit_ne_singleton, Matroid.Indep.mem_closure_iff, Matroid.closure_exchange, Matroid.isLoop_tfae, Matroid.isColoop_tfae]
  E1: auto
families: []
requires: [V03.C01, V03.C05, V04.C01, V04.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Circuits, closure and loops

### Overview

A matroid has several equivalent descriptions. The previous section gave the bases and the independent sets. This section gives three more: the *circuits*, which are the minimal dependent sets, the *closure* of a set, which is the set of elements that do not increase its rank, and the *flats*, which are the closed sets. In a graph the circuits are the edge sets of cycles, and in a vector space the closure of a set of vectors is the set of the vectors in its span.

The section ends with the elements of extreme type. A *loop* is an element that is in no base, and a *coloop* is an element that is in every base. In the dual matroid the two notions change places. Mathlib proves each of these facts for all matroids, finite or infinite, and the ground set conditions of the previous section stay important.

### The library around it

#### Circuits

The module `Mathlib.Combinatorics.Matroid.Circuit` defines `M.IsCircuit C` as `Minimal M.Dep C`. Each subset of the ground set is independent or contains a circuit, and two matroids with the same circuits are equal.

| Lean name | Statement |
| --- | --- |
| `Matroid.isCircuit_iff` | `M.IsCircuit C ↔ M.Dep C ∧ ∀ ⦃D⦄, M.Dep D → D ⊆ C → D = C` |
| `Matroid.dep_iff_superset_isCircuit` | for `X ⊆ M.E`, `M.Dep X ↔ ∃ C, C ⊆ X ∧ M.IsCircuit C` |
| `Matroid.IsCircuit.sdiff_singleton_isBasis` | for $e \in C$, the set `C \ {e}` is a basis of $C$ |
| `Matroid.ext_isCircuit` | equal ground sets and equal circuits give equal matroids |
| `Matroid.IsCircuit.elimination` | for circuits $C_1 \neq C_2$ and each $e$, a circuit is in `(C₁ ∪ C₂) \ {e}` |
| `Matroid.IsCircuit.strong_elimination` | for $e \in C_1 \cap C_2$ and $f \in C_1 \setminus C_2$, a circuit $C$ in `(C₁ ∪ C₂) \ {e}` has $f \in C$ |
| `Matroid.IsCircuit.strong_multi_elimination` | the strong elimination for a family of circuits $C_i$ and elements $x_i$ |
| `Matroid.finitary_iff_forall_isCircuit_finite` | `M.Finitary ↔ ∀ C, M.IsCircuit C → C.Finite` |

**Theorem.** If $C$ is a circuit and $e \in C$, then $C \setminus \{e\}$ is a basis of $C$.

*Proof.* The set $C \setminus \{e\}$ is a proper subset of $C$. By minimality it is not dependent, and it is a subset of $E$, so it is independent. The only independent set $J$ with $C \setminus \{e\} \subsetneq J \subseteq C$ is $J = C$, and $C$ is dependent. So $C \setminus \{e\}$ is a maximal independent subset of $C$. $\square$

#### Fundamental circuits

Let $I$ be independent and let $e \notin I$ be in the closure of $I$. Then `insert e I` contains exactly one circuit, the *fundamental circuit* `M.fundCircuit e I`. The definition gives a value for all $e$ and $I$. If $e \in I$, the value is the junk value `{e}`, by `Matroid.fundCircuit_eq_of_mem`.

| Lean name | Statement |
| --- | --- |
| `Matroid.mem_fundCircuit` | `e ∈ M.fundCircuit e I` |
| `Matroid.fundCircuit_subset_insert` | `M.fundCircuit e I ⊆ insert e I` |
| `Matroid.Indep.fundCircuit_isCircuit` | if `M.Indep I`, `e ∈ M.closure I` and `e ∉ I`, then `M.IsCircuit (M.fundCircuit e I)` |
| `Matroid.Indep.insert_isCircuit_of_forall` | `insert e I` is a circuit if $e$ is in the closure of $I$ and in no closure of `I \ {f}` |

#### Cocircuits

A *cocircuit* is a circuit of the dual: `M.IsCocircuit K` is the abbreviation of `M✶.IsCircuit K`. For a base $B$ and $e \in B$, the fundamental cocircuit `M.fundCocircuit e B` is the fundamental circuit of $e$ for the base `M✶.E \ B` of the dual.

| Lean name | Statement |
| --- | --- |
| `Matroid.dual_isCocircuit_iff` | `M✶.IsCocircuit C ↔ M.IsCircuit C` |
| `Matroid.IsCircuit.inter_isCocircuit_ne_singleton` | a circuit and a cocircuit do not meet in exactly one element |
| `Matroid.IsBase.mem_fundCocircuit_iff_mem_fundCircuit` | for a base $B$, `e ∈ M.fundCocircuit f B ↔ f ∈ M.fundCircuit e B` |

#### Closure and flats

The module `Mathlib.Combinatorics.Matroid.Closure` defines flats first. The structure `M.IsFlat F` has two fields: `F ⊆ M.E`, and each set $X$ that has a basis in common with $F$ is a subset of $F$. The closure is the intersection of the flats that contain `X ∩ M.E`:

`M.closure X = ⋂₀ {F | M.IsFlat F ∧ X ∩ M.E ⊆ F}`.

The intersection with `M.E` makes `M.closure` a total function on `Set α`. The term `M.subtypeClosure` is the same operation as a `ClosureOperator` on the interval `Iic M.E`, and `Matroid.isFlat_iff_isClosed` says that its closed elements are the flats.

| Lean name | Statement |
| --- | --- |
| `Matroid.closure_inter_ground` | `M.closure (X ∩ M.E) = M.closure X` |
| `Matroid.closure_subset_ground` | `M.closure X ⊆ M.E` |
| `Matroid.subset_closure` | `X ⊆ M.closure X`, for `X ⊆ M.E` |
| `Matroid.closure_mono` | `Monotone M.closure` |
| `Matroid.closure_closure` | `M.closure (M.closure X) = M.closure X` |
| `Matroid.isFlat_iff_closure_eq` | `M.IsFlat F ↔ M.closure F = F` |
| `Matroid.Indep.mem_closure_iff` | for independent $I$, `x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I` |
| `Matroid.Indep.insert_indep_iff` | for independent $I$, `M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I` |
| `Matroid.mem_closure_iff_exists_isCircuit` | for $e \notin X$, $e$ is in the closure of $X$ if and only if a circuit $C \subseteq$ `insert e X` contains $e$ |
| `Matroid.closure_exchange` | `e ∈ M.closure (insert f X) \ M.closure X → f ∈ M.closure (insert e X) \ M.closure X` |
| `Matroid.ext_closure` | two matroids with the same closure function are equal |

The lemma `Matroid.closure_exchange` is the exchange property of closure. On paper, this property together with monotonicity, idempotence and `subset_closure` is a set of axioms for finite matroids in terms of closure.

#### Spanning sets

A set $S$ is *spanning*, `M.Spanning S`, if `M.closure S = M.E` and `S ⊆ M.E`. The bases are the independent spanning sets and the minimal spanning sets.

| Lean name | Statement |
| --- | --- |
| `Matroid.IsBase.closure_eq` | `M.IsBase B → M.closure B = M.E` |
| `Matroid.Indep.isBase_of_spanning` | an independent spanning set is a base |
| `Matroid.isBase_iff_minimal_spanning` | `M.IsBase B ↔ Minimal M.Spanning B` |
| `Matroid.coindep_iff_compl_spanning` | for `I ⊆ M.E`, `M.Coindep I ↔ M.Spanning (M.E \ I)` |

#### Loops and coloops

The module `Mathlib.Combinatorics.Matroid.Loop` defines `M.loops` as `M.closure ∅` and `M.IsLoop e` as `e ∈ M.loops`. The structure `M.IsNonloop e` has the fields `¬ M.IsLoop e` and `e ∈ M.E`. A coloop is a loop of the dual: `M.IsColoop e` is `M✶.IsLoop e`, and `M.coloops` is `M✶.loops`.

| Lean name | Statement |
| --- | --- |
| `Matroid.isLoop_tfae` | the conditions `M.IsLoop e`, `e ∈ M.closure ∅`, `M.IsCircuit {e}`, `M.Dep {e}` and "$e \in E \setminus B$ for each base $B$" are equivalent |
| `Matroid.singleton_isCircuit` | `M.IsCircuit {e} ↔ M.IsLoop e` |
| `Matroid.indep_singleton` | `M.Indep {e} ↔ M.IsNonloop e` |
| `Matroid.isLoop_or_isNonloop` | for `e ∈ M.E`, `M.IsLoop e ∨ M.IsNonloop e` |
| `Matroid.Indep.disjoint_loops` | an independent set contains no loop |
| `Matroid.isColoop_tfae` | seven equivalent conditions, among them `M.IsCocircuit {e}`, "$e$ is in each base" and "$e$ is in no circuit and $e \in E$" |
| `Matroid.isColoop_iff_forall_mem_isBase` | `M.IsColoop e ↔ ∀ ⦃B⦄, M.IsBase B → e ∈ B` |
| `Matroid.dual_isLoop_iff_isColoop` | `M✶.IsLoop e ↔ M.IsColoop e` |
| `Matroid.loopless_iff_forall_isCircuit` | `M.Loopless ↔ ∀ C, M.IsCircuit C → C.Nontrivial` |

**Theorem.** A loop is in no base.

*Proof.* Let $e$ be a loop and $B$ a base with $e \in B$. Then $\{e\} \subseteq B$, and $\{e\}$ is independent because $B$ is independent. This contradicts `Matroid.singleton_isCircuit`, since a circuit is dependent. $\square$

The class `M.Loopless` says that `M.loops = ∅`. The matroid `M.removeLoops` is the restriction `M ↾ {e | M.IsNonloop e}`, and the instance `Matroid.removeLoops_loopless` makes it loopless. Restriction is the subject of the next section.

#### Common errors

1. A learner applies `Matroid.subset_closure` to a set that is not in the ground set. The closure ignores the part of $X$ outside `M.E`, so `X ⊆ M.closure X` is false in general. Rewrite with `Matroid.closure_inter_ground` and use `X ∩ M.E`.
2. A learner uses `M.fundCircuit e I` without the hypotheses of `Matroid.Indep.fundCircuit_isCircuit`. If $e \in I$ the value is `{e}`, and that set is a circuit only if $e$ is a loop.
3. A learner proves `¬ M.IsLoop e` and expects `M.IsNonloop e`. An element outside `M.E` is neither a loop nor a nonloop, and `Matroid.not_isLoop_iff` needs `e ∈ M.E`.

### Exercises

1. (A) Prove that the loops of `loopyOn E` are the elements of $E$ and that `freeOn E` has no loops, from `Matroid.loopyOn_isLoop_iff` and `Matroid.freeOn_not_isLoop`.
2. (A) Prove that a coloop is in no circuit, from `Matroid.isColoop_tfae`.
3. (B) Prove that the closure of a base is the ground set, and deduce that a superset of a base in `M.E` is spanning.
4. (B) Let $e \neq f$ be nonloops. Prove that `M.closure {e} = M.closure {f}` if and only if `{e, f}` is a circuit, as in `Matroid.IsNonloop.closure_eq_closure_iff_isCircuit_of_ne`.
5. (B) Prove `Matroid.IsCircuit.elimination` from `Matroid.IsCircuit.strong_elimination`.
6. (C) Prove `Matroid.IsCircuit.inter_isCocircuit_ne_singleton` for a finite matroid, from the description of cocircuits as complements of hyperplanes.

### Reference

<?reference?>
