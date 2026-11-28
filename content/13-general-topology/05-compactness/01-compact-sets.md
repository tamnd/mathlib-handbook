---
title: Compact sets
kind: theory
modules:
  - Mathlib.Topology.Compactness.Compact
  - Mathlib.Topology.Order.Compact
  - Mathlib.Topology.Maps.Proper.Basic
  - Mathlib.Topology.Maps.Proper.CompactlyGenerated
  - Mathlib.Topology.Maps.Proper.UniversallyClosed
explains:
  E3: [IsCompact, CompactSpace]
  E2: [isCompact_iff_finite_subcover, IsCompact.elim_finite_subcover, isCompact_iff_finite_subfamily_closed, IsCompact.exists_clusterPt, isCompact_iff_compactSpace, IsCompact.of_isClosed_subset, IsClosed.isCompact, IsCompact.image, isCompact_singleton, Set.Finite.isCompact, IsCompact.union, IsCompact.isClosed, SeparatedNhds.of_isCompact_isCompact, NormalSpace.of_compactSpace_r1Space, Continuous.isClosedMap, Continuous.homeoOfEquivCompactToT2, IsCompact.exists_isMinOn, IsCompact.exists_isMaxOn]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Compact sets

### Overview

The classical definition of compactness uses open covers. The definition of Mathlib uses filters: a set $K$ is compact if each proper filter that contains $K$ has a cluster point in $K$. For a sequence, the filter of its tails is such a filter, and a cluster point is the limit of a subnet; so the filter definition is the general form of "each sequence has a convergent subsequence". This section proves that the two definitions agree, and then proves the basic theorems with whichever definition is shorter.

### Definitions

**Definition (Compact set, compact space).** A set $K$ in a space $X$ is compact if for each proper filter $F$ on $X$ with $F \le \mathcal{P}(K)$, there is an $x \in K$ that is a cluster point of $F$. The space $X$ is compact if $X$ is a compact set.

*Remarks.* The condition $F \le \mathcal{P}(K)$ says $K \in F$. A compact space need not be Hausdorff, and many texts add the Hausdorff axiom to the definition. Mathlib does not.

::: mathlib
`IsCompact` · `Mathlib.Topology.Defs.Filter`

`IsCompact s` is `∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f`. The lemma `IsCompact.exists_clusterPt` applies it.

<?decl IsCompact?>
:::

::: mathlib
`IsCompact.exists_clusterPt` · `Mathlib.Topology.Compactness.Compact`

The definition as a usable lemma.

<?decl IsCompact.exists_clusterPt?>
:::

::: mathlib
`CompactSpace` · `Mathlib.Topology.Defs.Filter`

A class with the field `isCompact_univ`. A compact set gives a compact subtype and back: `isCompact_iff_compactSpace`.

<?decl CompactSpace?>
:::

::: mathlib
`isCompact_iff_compactSpace` · `Mathlib.Topology.Compactness.Compact`

A set is compact if and only if the subtype is a compact space.

<?decl isCompact_iff_compactSpace?>
:::

### Theorems and proofs

**Theorem (Open covers).** A set $K \subseteq X$ is compact if and only if each family of open sets that covers $K$ has a finite subfamily that covers $K$.

*Proof.* Assume $K$ is compact, and let $(U_i)_{i \in I}$ be open sets that cover $K$. Suppose that no finite subfamily covers $K$. Then each set $K \setminus (U_{i_1} \cup \dots \cup U_{i_n})$ is nonempty. These sets are closed under finite intersections. By the theorem on generated filters of Chapter 2, they generate a proper filter $F$, and $K \in F$ (the case $n = 0$). By compactness $F$ has a cluster point $x \in K$. Choose $j$ with $x \in U_j$. Then $U_j \in \mathcal{N}(x)$ and $K \setminus U_j \in F$ are disjoint, which contradicts the cluster point property.

Conversely, assume the cover property, and let $F$ be a proper filter with $K \in F$. Suppose that no point of $K$ is a cluster point of $F$. For each $x \in K$ there is then an open $U_x \ni x$ and an $A_x \in F$ with $U_x \cap A_x = \emptyset$. The $U_x$ cover $K$, so finitely many $U_{x_1}, \dots, U_{x_n}$ cover $K$. The set $A = K \cap A_{x_1} \cap \dots \cap A_{x_n}$ is in $F$. It lies in $K \subseteq U_{x_1} \cup \dots \cup U_{x_n}$ and misses each $U_{x_k}$. So $A = \emptyset$, against the properness of $F$. $\square$

::: mathlib
`isCompact_iff_finite_subcover` · `Mathlib.Topology.Compactness.Compact`

The theorem, with a family indexed by a type in the universe of `X` and a `Finset` of indices. `IsCompact.elim_finite_subcover` is the direction from compactness.

<?decl isCompact_iff_finite_subcover?>
:::

::: mathlib
`IsCompact.elim_finite_subcover` · `Mathlib.Topology.Compactness.Compact`

A compact set and an open cover give a finite subcover.

<?decl IsCompact.elim_finite_subcover?>
:::

::: mathlib
`isCompact_iff_finite_subfamily_closed` · `Mathlib.Topology.Compactness.Compact`

The dual form with closed sets: if a family of closed sets has an intersection that misses `s`, then so has a finite subfamily. For `s = univ` it is the finite intersection property.

<?decl isCompact_iff_finite_subfamily_closed?>
:::

**Theorem (Closed subsets, images, unions).** Let $K$ be compact.

1. A closed set $C \subseteq K$ is compact. In a compact space each closed set is compact.
2. If $f : X \to Y$ is continuous, then $f(K)$ is compact.
3. Finite sets are compact, and a finite union of compact sets is compact.

*Proof.* (1) Let $F$ be proper with $C \in F$. Then $K \in F$, so $F$ has a cluster point $x \in K$. Each neighbourhood of $x$ meets each member of $F$, and in particular meets $C$. So $x \in \overline{C} = C$.

(2) Let $G$ be a proper filter on $Y$ with $f(K) \in G$. The family $\{f^{-1}(B) : B \in G\}$ generates the filter $f^{*}G$. It is proper: $f^{-1}(B) \cap K \ne \emptyset$ for each $B \in G$, because $B \cap f(K) \in G$ is nonempty. So $F = f^{*}G \sqcap \mathcal{P}(K)$ is proper, and $K \in F$. Let $x \in K$ be a cluster point of $F$. For a neighbourhood $V$ of $f(x)$ and $B \in G$, the set $f^{-1}(V)$ is a neighbourhood of $x$, so it meets $f^{-1}(B) \cap K$. So $V \cap B \ne \emptyset$, and $f(x) \in f(K)$ is a cluster point of $G$.

(3) Use open covers: a cover of a finite union has a finite subcover for each piece, and their union is finite. A point is compact, so a finite set is a finite union of compact sets. $\square$

::: mathlib
`IsCompact.of_isClosed_subset` · `Mathlib.Topology.Compactness.Compact`

Part 1. The form for a compact space is `IsClosed.isCompact`.

<?decl IsCompact.of_isClosed_subset?>
:::

::: mathlib
`IsCompact.image` · `Mathlib.Topology.Compactness.Compact`

Part 2. The variant `IsCompact.image_of_continuousOn` asks continuity only on the set.

<?decl IsCompact.image?>
:::

::: mathlib
`IsCompact.union` · `Mathlib.Topology.Compactness.Compact`

Part 3 for two sets. `Set.Finite.isCompact` and `isCompact_singleton` give the finite sets.

<?decl IsCompact.union?>
:::

**Theorem (Compact sets in Hausdorff spaces).** Let $X$ be Hausdorff.

1. Two disjoint compact sets $K, L$ have disjoint open neighbourhoods.
2. Each compact set is closed.
3. A compact Hausdorff space is normal.

*Proof.* (1) First let $L = \{y\}$ with $y \notin K$. For each $x \in K$ choose disjoint open sets $U_x \ni x$ and $V_x \ni y$. Finitely many $U_{x_1}, \dots, U_{x_n}$ cover $K$. Then $U = \bigcup_k U_{x_k} \supseteq K$ and $V = \bigcap_k V_{x_k} \ni y$ are open and disjoint. For general $L$, for each $y \in L$ choose disjoint open $U_y \supseteq K$ and $V_y \ni y$ by the first case. Finitely many $V_{y_1}, \dots, V_{y_m}$ cover $L$. Then $\bigcap_k U_{y_k}$ and $\bigcup_k V_{y_k}$ work.

(2) For $y \notin K$, part 1 with $L = \{y\}$ gives an open $V \ni y$ that misses $K$. So $X \setminus K$ is open.

(3) In a compact space, closed sets are compact by the previous theorem. Part 1 separates two disjoint closed sets. $\square$

::: mathlib
`IsCompact.isClosed` · `Mathlib.Topology.Separation.Hausdorff`

Part 2. In a non-Hausdorff space it fails: in the cofinite topology on `ℕ` each set is compact.

<?decl IsCompact.isClosed?>
:::

::: mathlib
`SeparatedNhds.of_isCompact_isCompact` · `Mathlib.Topology.Separation.Hausdorff`

Part 1.

<?decl SeparatedNhds.of_isCompact_isCompact?>
:::

::: mathlib
`NormalSpace.of_compactSpace_r1Space` · `Mathlib.Topology.Separation.Regular`

Part 3, as an instance under the weaker axiom $R_1$ of Chapter 4.

<?decl NormalSpace.of_compactSpace_r1Space?>
:::

**Corollary (Compact to Hausdorff).** Let $X$ be compact, $Y$ Hausdorff and $f : X \to Y$ continuous. Then $f$ is a closed map. If $f$ is bijective, it is a homeomorphism.

*Proof.* A closed $C \subseteq X$ is compact, so $f(C)$ is compact, so $f(C)$ is closed. If $f$ is bijective, then $(f^{-1})^{-1}(C) = f(C)$ is closed for each closed $C$, so $f^{-1}$ is continuous. $\square$

::: mathlib
`Continuous.isClosedMap` · `Mathlib.Topology.Separation.Hausdorff`

A continuous map from a compact space to a Hausdorff space is closed.

<?decl Continuous.isClosedMap?>
:::

::: mathlib
`Continuous.homeoOfEquivCompactToT2` · `Mathlib.Topology.Homeomorph.Lemmas`

The homeomorphism built from a continuous equivalence of a compact space with a Hausdorff space.

<?decl Continuous.homeoOfEquivCompactToT2?>
:::

**Theorem (Extreme value theorem).** Let $K$ be compact and nonempty and $f : X \to \mathbb{R}$ continuous. Then $f$ has a minimum and a maximum on $K$.

*Proof.* The set $f(K)$ is compact in $\mathbb{R}$, hence closed. It is bounded: the open intervals $(-n, n)$ cover it, and finitely many do. Since it is nonempty and bounded, $m = \inf f(K)$ exists (Volume 4), and $m \in \overline{f(K)} = f(K)$. So $m = f(x)$ for some $x \in K$. The maximum is the same. $\square$

::: mathlib
`IsCompact.exists_isMinOn` · `Mathlib.Topology.Order.Compact`

The theorem for a function into a linear order with a closed order topology, continuous on the set.

<?decl IsCompact.exists_isMinOn?>
:::

::: mathlib
`IsCompact.exists_isMaxOn` · `Mathlib.Topology.Order.Compact`

The maximum.

<?decl IsCompact.exists_isMaxOn?>
:::

### Examples

**Example (The cofinite topology).** Each subset $A$ of a space with the cofinite topology is compact. Let $(U_i)$ be an open cover of $A$, with $A$ nonempty. One $U_{i_0}$ contains a point of $A$, and it misses only finitely many points $a_1, \dots, a_n$ of $A$. Choose $U_{i_k} \ni a_k$. Then $U_{i_0}, \dots, U_{i_n}$ cover $A$. On an infinite set, $\mathbb{N} \setminus \{0\}$ is compact and not closed, so the Hausdorff axiom in part 2 of the theorem is needed.

**Counterexample ($\mathbb{R}$ and $(0, 1)$).** The open intervals $(-n, n)$ cover $\mathbb{R}$ with no finite subcover, so $\mathbb{R}$ is not compact. The intervals $(1/n, 1)$ cover $(0, 1)$ with no finite subcover. In filter form, the filter $\mathcal{N}_{>}(0) \sqcap \mathcal{P}((0,1))$ is proper, contains $(0, 1)$, and its only cluster point in $\mathbb{R}$ is $0 \notin (0, 1)$.

**Example (A continuous bijection again).** The map $[0, 1) \to S^1$ of Chapter 1 is a continuous bijection and not a homeomorphism. The corollary does not apply: $[0, 1)$ is not compact. The map $[0, 1]/{\sim} \to S^1$ that identifies the ends is a homeomorphism, by the corollary.

### The library around it

The definition is in `Mathlib.Topology.Defs.Filter`, and the general theory in `Mathlib.Topology.Compactness.Compact`. The extreme value theorem and the compactness of intervals are in `Mathlib.Topology.Order.Compact`. Local compactness, `LocallyCompactSpace`, and σ-compactness are in the same folder `Mathlib.Topology.Compactness`. The homeomorphism criterion is in `Mathlib.Topology.Homeomorph.Lemmas`.

Mathlib proves most results on compactness with the filter definition, or with one of the induction principles `IsCompact.induction_on`, which proves a property of a compact set from its local form. The open cover form is used when a statement is about covers.

A proper map is the relative form of a compact space. The structure `IsProperMap f` says that $f : X \to Y$ is continuous and that each filter $\mathcal{F}$ on $X$ whose image clusters at $y$ clusters at some point $x$ with $f(x) = y$ (`IsProperMap.clusterPt_of_mapClusterPt`). The definition is in `Mathlib.Topology.Maps.Proper.Basic`, with its main consequences: a proper map is closed (`IsProperMap.isClosedMap`), the preimage of a compact set is compact (`IsProperMap.isCompact_preimage`), and the range is closed (`IsProperMap.isClosed_range`). The characterization `isProperMap_iff_isClosedMap_and_compact_fibers` says that $f$ is proper if and only if it is continuous, closed, and has compact fibres. The ultrafilter form `isProperMap_iff_ultrafilter` follows the ultrafilter definition of compactness. Proper maps compose (`IsProperMap.comp`), form products (`IsProperMap.prodMap`, `IsProperMap.pi_map`) and restrict to closed sets (`IsProperMap.restrict`). Closed embeddings and homeomorphisms are proper (`Topology.IsClosedEmbedding.isProperMap`, `Homeomorph.isProperMap`), and a continuous map from a compact space to a Hausdorff space is proper (`Continuous.isProperMap`). A constant map is proper exactly when its domain is compact (`isProperMap_const_iff`). The same module proves the closed graph theorem for a compact Hausdorff target: `continuous_iff_isClosed_graph`. The module `Mathlib.Topology.Maps.Proper.CompactlyGenerated` gives the classical definition for a Hausdorff compactly coherent target: `isProperMap_iff_isCompact_preimage` says that $f$ is proper if and only if it is continuous and preimages of compact sets are compact. The module `Mathlib.Topology.Maps.Proper.UniversallyClosed` proves that $f$ is proper if and only if it is continuous and $f \times \mathrm{id}_Z$ is closed for each space $Z$ (`isProperMap_iff_universally_closed`).

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that a set $K \subseteq \mathbb{R}$ with a sequence $x_n \in K$ and $|x_n| \to \infty$ is not compact.
2. (A) Show that $\{0\} \cup \{1/n : n \ge 1\}$ is compact with the open cover definition.
3. (A) Show that an intersection of a compact set and a closed set is compact.
4. (B) Show that a compact subset of a metric space is bounded and closed.
5. (B) Show that a space is compact if and only if each family of closed sets with the finite intersection property has a nonempty intersection.
6. (B) Let $X$ be compact and $f : X \to \mathbb{R}$ be such that each point has a neighbourhood on which $f$ is bounded. Show that $f$ is bounded.
7. (C) Show that a compact Hausdorff space has no strictly coarser Hausdorff topology and no strictly finer compact topology.

### Notes and history

The open cover definition comes from the Borel-Lebesgue lemma: Borel (1895) proved that a countable open cover of $[a, b]$ has a finite subcover, and Lebesgue (1904) removed the countability. Alexandroff and Urysohn (1923 to 1929) made the open cover property the definition of a "bicompact" space. Cartan and Bourbaki gave the filter definition. The extreme value theorem is due to Weierstrass, in his lectures of the 1860s.

### Reference

<?reference?>
