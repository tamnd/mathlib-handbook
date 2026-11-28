---
title: Local compactness, σ-compactness and paracompactness
kind: api
modules:
  - Mathlib.Topology.Compactness.LocallyCompact
  - Mathlib.Topology.Compactness.SigmaCompact
  - Mathlib.Topology.Compactness.Paracompact
  - Mathlib.Topology.Compactness.LocallyFinite
  - Mathlib.Topology.Compactness.Bases
  - Mathlib.Topology.Compactness.NhdsKer
explains:
  E2: [exists_compact_between, compact_basis_nhds, CompactExhaustion.choice, LocallyFinite.countable_univ, precise_refinement, paracompact_of_locallyCompact_sigmaCompact, isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis, IsCompact.nhdsKer_iff]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Local compactness, σ-compactness and paracompactness

### Overview

Most spaces of analysis are not compact. The real line, an open subset of $\mathbb{R}^n$ and a manifold are not compact, but they are made of compact pieces. This section gives the three conditions that make this idea exact.

A space is *locally compact* if each neighborhood of each point contains a compact neighborhood of that point. A space is *σ-compact* if it is a countable union of compact sets. A space is *paracompact* if each open cover has a locally finite open refinement. The three conditions are related by one theorem: a Hausdorff space that is locally compact and σ-compact is paracompact. Paracompactness is the condition that gives partitions of unity, and the partitions of unity of Volume 23 start from it.

The section also gives compact exhaustions, the countability of locally finite families in a σ-compact space, compact open sets in a space with a compact basis, and the compactness of the neighborhood kernel of a set. It uses compact sets from Section 1, neighborhood filters from Chapter 2 and the separation axioms of Chapter 4.

### The library around it

#### Locally compact spaces

The classes are in `Mathlib.Topology.Defs.Filter`, and their theory is in `Mathlib.Topology.Compactness.LocallyCompact`. There are three classes.

- `WeaklyLocallyCompactSpace X`: each point has one compact neighborhood. The field is `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`.
- `LocallyCompactSpace X`: each neighborhood of $x$ contains a compact neighborhood of $x$. The field is `local_compact_nhds`.
- `LocallyCompactPair X Y`: for each continuous map $f : X \to Y$ and each neighborhood $s$ of $f(x)$, there is a compact neighborhood $K$ of $x$ with $f(K) \subseteq s$. The field is `LocallyCompactPair.exists_mem_nhds_isCompact_mapsTo`.

The instance `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace` gives the weak form from the strong one, and `instLocallyCompactPairOfLocallyCompactSpace` gives the pair form from a locally compact source. A compact space is weakly locally compact by `instWeaklyLocallyCompactSpaceOfCompactSpace`. In an $R_1$ space, for example a Hausdorff space, the weak form gives the strong form by `WeaklyLocallyCompactSpace.locallyCompactSpace`, and the space is regular by `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`. The library keeps the two classes because some theorems need only the weak form, and the weak form has no separation hypothesis.

The class `LocallyCompactPair` is the hypothesis that Section 1 of Chapter 11 uses for the continuity of evaluation on `C(X, Y)`. It follows from local compactness of $X$. It also holds when $X$ is only weakly locally compact and $Y$ is an $R_1$ space, by `instLocallyCompactPairOfWeaklyLocallyCompactSpaceOfR1Space`.

The basic theorems turn the definition into a basis statement:

- `compact_basis_nhds`: in a locally compact space, the compact neighborhoods of $x$ form a basis of `nhds x`;
- `exists_compact_subset`: each open set $U$ that contains $x$ contains a compact set $K$ with $x$ in the interior of $K$;
- `exists_compact_between`: if $K$ is compact, $U$ is open and $K \subseteq U$, there is a compact $L$ with $K \subseteq \operatorname{interior} L$ and $L \subseteq U$;
- `IsCompact.nhdsSet_basis_isCompact`: the compact neighborhoods of a compact set form a basis of its filter of neighborhoods;
- `exists_compact_superset`: in a weakly locally compact space, each compact set is in the interior of a compact set.

**Theorem.** Let $X$ be locally compact, $K \subseteq X$ compact and $U \supseteq K$ open. Then there is a compact $L$ with $K \subseteq \operatorname{interior} L \subseteq L \subseteq U$.

*Proof sketch.* For each $x \in K$ choose a compact neighborhood $L_x \subseteq U$ of $x$ by `exists_compact_subset`. The interiors of the $L_x$ cover $K$, so finitely many of them cover $K$. The union $L$ of the finitely many $L_x$ is compact, it is in $U$, and its interior contains $K$.

The class is stable under the usual constructions. Open subsets, closed subsets and locally closed subsets of a locally compact space are locally compact (`IsOpen.locallyCompactSpace`, `IsClosed.locallyCompactSpace`, `IsLocallyClosed.locallyCompactSpace`). Finite products are locally compact by `Prod.locallyCompactSpace` and `Pi.locallyCompactSpace_of_finite`. An infinite product is locally compact when all the factors are compact, by `Pi.locallyCompactSpace`. Open embeddings, closed embeddings and open quotient maps transfer the class: `Topology.IsOpenEmbedding.locallyCompactSpace`, `Topology.IsClosedEmbedding.locallyCompactSpace` and `IsOpenQuotientMap.locallyCompactSpace`.

The filter `Filter.cocompact X` of Section 1 meets local compactness in `disjoint_nhds_cocompact`: in a weakly locally compact space, the neighborhood filter of a point is disjoint from the cocompact filter. Section 7 uses this fact to separate the new point of the one-point compactification from the points of the space.

#### σ-compact spaces and compact exhaustions

The module `Mathlib.Topology.Compactness.SigmaCompact` defines `IsSigmaCompact s`, the statement that $s$ is a countable union of compact sets, and the class `SigmaCompactSpace X`, the statement that `Set.univ` is σ-compact. The predicate on sets has the usual closure rules: `IsCompact.isSigmaCompact`, `isSigmaCompact_iUnion`, `isSigmaCompact_sUnion_of_isCompact`, `IsSigmaCompact.image`, `IsSigmaCompact.of_isClosed_subset` and `isSigmaCompact_iff_sigmaCompactSpace`. A space is σ-compact if it is compact (`CompactSpace.sigmaCompact`) or if it is locally compact and second countable (`sigmaCompactSpace_of_locallyCompact_secondCountable`).

In a σ-compact space, the function `compactCovering X` gives a chosen increasing sequence of compact sets with union `Set.univ`. The lemmas are `isCompact_compactCovering`, `iUnion_compactCovering` and `compactCovering_subset`. The sequence has no interior condition. For that, the structure `CompactExhaustion X` gives a sequence $K_n$ of compact sets with $K_n \subseteq \operatorname{interior} K_{n+1}$ and union `Set.univ`. The definition `CompactExhaustion.choice` builds one in a space that is weakly locally compact and σ-compact. The main facts are:

- `CompactExhaustion.subset_interior_succ` and `CompactExhaustion.iUnion_eq`, the two fields;
- `CompactExhaustion.exists_superset_of_isCompact`: each compact set is in some $K_n$;
- `CompactExhaustion.exists_mem_nhds`: each point has some $K_n$ as a neighborhood;
- `CompactExhaustion.find`, the first index $n$ with $x \in K_n$, with `CompactExhaustion.mem_find` and `CompactExhaustion.mem_iff_find_le`;
- `CompactExhaustion.shiftr`, the exhaustion with $\emptyset$ put first.

A compact exhaustion is a coercion to `ℕ → Set X` through `CompactExhaustion.instFunLikeNatSet`, so `K n` is the $n$-th set.

Two countability results come from σ-compactness. The theorem `countable_cover_nhds_of_sigmaCompact` gives a countable set of points $s$ such that the neighborhoods $f(x)$ for $x \in s$ cover $X$. The theorem `LocallyFinite.countable_univ` says that a locally finite family of nonempty sets in a σ-compact space has a countable index set. The proof uses `LocallyFinite.finite_nonempty_inter_compact` from `Mathlib.Topology.Compactness.LocallyFinite`: a compact set meets only finitely many sets of a locally finite family. Then each compact set of a countable compact cover meets finitely many members. In a compact space, `LocallyFinite.finite_nonempty_of_compact` gives directly that only finitely many members are nonempty.

#### Paracompact spaces

The module `Mathlib.Topology.Compactness.Paracompact` defines the class `ParacompactSpace X`. Its field `ParacompactSpace.locallyFinite_refinement` says that each open cover $s : \alpha \to \operatorname{Set} X$ has an open cover $t : \beta \to \operatorname{Set} X$ that is locally finite and that refines $s$: each $t(b)$ is in some $s(a)$. The form that is used in practice is `precise_refinement`: the refinement can be indexed by the same type $\iota$, with $v(i) \subseteq u(i)$ for each $i$. The variant `precise_refinement_set` covers a closed set and not the whole space.

The instances and transfer results are:

- `paracompact_of_compact`: a compact space is paracompact;
- `paracompact_of_locallyCompact_sigmaCompact`: a weakly locally compact, σ-compact Hausdorff space is paracompact;
- `Topology.IsClosedEmbedding.paracompactSpace` and `Homeomorph.paracompactSpace_iff`: closed subspaces and homeomorphic spaces;
- `instParacompactSpaceProdOfCompactSpace`: the product of a compact space and a paracompact space;
- `NormalSpace.of_paracompactSpace_r1Space`: a paracompact $R_1$ space is normal.

The paracompactness of metric spaces, the theorem of Stone, is in `Mathlib.Topology.EMetricSpace.Paracompact`, and Chapter 3 describes it.

**Theorem.** A Hausdorff space $X$ that is weakly locally compact and σ-compact is paracompact.

*Proof sketch.* Take a compact exhaustion $K_n$ by `CompactExhaustion.choice`. For each $n$, the compact set $K_{n+1} \setminus \operatorname{interior} K_n$ is in the open set $\operatorname{interior} K_{n+2} \setminus K_{n-1}$. Cover it by finitely many members of the given cover, each one cut down to this open set. The union of these finite families over all $n$ covers $X$, and it is locally finite because a point in $\operatorname{interior} K_n$ meets only the families of index at most $n + 1$. The library proves the stronger `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis`, which takes the refinement from a given basis of neighborhoods at each point.

#### Compact bases and the neighborhood kernel

The module `Mathlib.Topology.Compactness.Bases` has one theorem. If the range of $b$ is a basis of the topology and each $b(i)$ is compact, then `isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis` says that a set is compact and open if and only if it is a finite union of sets $b(i)$. The proof is one step in each direction: a compact open set is covered by the basic sets in it, so finitely many of them are enough, and a finite union of compact open sets is compact and open. Chapter 1 gives the same theorem in the language of `TopologicalSpace.Opens`.

The module `Mathlib.Topology.Compactness.NhdsKer` uses the neighborhood kernel `nhdsKer s`, the intersection of all neighborhoods of $s$. The theorem `IsCompact.nhdsKer_iff` says that `nhdsKer s` is compact if and only if $s$ is compact. The two directions are `IsCompact.nhdsKer` and `IsCompact.of_nhdsKer`. In a $T_1$ space `nhdsKer s` equals $s$, so the theorem is of interest only for spaces such as the Alexandrov discrete spaces of Chapter 1.

#### Common errors

1. Using `LocallyCompactSpace` where `WeaklyLocallyCompactSpace` is enough. Many theorems, for example `CompactExhaustion.choice` and `paracompact_of_locallyCompact_sigmaCompact`, take only the weak class. A hypothesis of the strong class still works through the instance, but a lemma stated with the strong class cannot be used for a compact space that is not $R_1$.
2. Applying the field `ParacompactSpace.locallyFinite_refinement` directly. The index types $\alpha$ and $\beta$ must be in the same universe as $X$, and the refinement has a new index type. Use `precise_refinement`, which keeps the index type of the cover.
3. Confusing `compactCovering X` with a compact exhaustion. The sets `compactCovering X n` are compact and increasing, but a point need not be in the interior of any of them. Use `CompactExhaustion.choice` when the interior condition is necessary.

### Exercises

1. (A) Use `compact_basis_nhds` to prove that each point of a locally compact space has a compact neighborhood. Then find the instance that gives `WeaklyLocallyCompactSpace X` from `LocallyCompactSpace X`.
2. (A) Show that $\mathbb{R}$ is σ-compact with the sets $[-n, n]$, and find the instance that Lean uses for `SigmaCompactSpace ℝ`.
3. (B) Prove `exists_compact_between` from `exists_compact_subset` and `IsCompact.elim_finite_subcover`.
4. (B) Let $X$ be σ-compact and let $f$ be a locally finite family of nonempty sets. Prove that the index type is countable, with `LocallyFinite.finite_nonempty_inter_compact` and `iUnion_compactCovering`.
5. (B) Use `isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis` to show that, in a discrete space with the basis of singletons, the compact open sets are the finite sets.
6. (C) Prove that a weakly locally compact, σ-compact Hausdorff space is normal, with the instances of this section and of Chapter 4.

### Reference

<?reference?>
