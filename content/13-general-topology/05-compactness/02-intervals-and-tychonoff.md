---
title: Compactness of intervals and the Tychonoff theorem
kind: theory
modules:
  - Mathlib.Topology.Order.Compact
  - Mathlib.Topology.UnitInterval
  - Mathlib.Topology.IsClosedRestrict
explains:
  E3: [CompactIccSpace]
  E2: [CompactIccSpace.isCompact_Icc, ConditionallyCompleteLinearOrder.toCompactIccSpace, unitInterval, isCompact_iff_ultrafilter_le_nhds, Ultrafilter.le_nhds_lim, nhds_pi, tendsto_pi_nhds, isCompact_univ_pi, isCompact_pi_infinite, Pi.compactSpace, IsCompact.prod]
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

## Compactness of intervals and the Tychonoff theorem

### Overview

This section proves the two main compactness theorems of general topology. The first says that a closed bounded interval $[a, b]$ of $\mathbb{R}$ is compact. The proof uses the filter definition and the least upper bound property, and it works in each conditionally complete linear order. The second, the Tychonoff theorem, says that each product of compact spaces is compact. The proof uses ultrafilters: in a product, an ultrafilter converges if each of its projections converges, and each projection converges by compactness of the factor.

### Definitions

**Definition (Compact intervals).** A preordered space $X$ has compact intervals if each closed interval $[a, b] = \{x : a \le x \le b\}$ is compact.

::: mathlib
`CompactIccSpace` · `Mathlib.Topology.Order.Compact`

The class says that each `Set.Icc a b` is compact. Its field is `CompactIccSpace.isCompact_Icc`, and the theorem below gives the instance for each conditionally complete linear order with the order topology, so for `ℝ`.

<?decl CompactIccSpace?>
:::

::: mathlib
`CompactIccSpace.isCompact_Icc` · `Mathlib.Topology.Order.Compact`

A closed interval is compact. This is the lemma that a proof uses to get the compactness of `Set.Icc a b` in `ℝ`.

<?decl CompactIccSpace.isCompact_Icc?>
:::

::: mathlib
`unitInterval` · `Mathlib.Topology.UnitInterval`

The set `Icc 0 1` in `ℝ`, written `I` after `open unitInterval`. As a type it is compact by the theorem, and it is the domain of paths in Chapter 6.

<?decl unitInterval?>
:::

### Theorems and proofs

**Theorem (Compactness of $[a, b]$).** Let $a \le b$ be real numbers. Then $[a, b]$ is compact.

*Proof.* Let $F$ be a proper filter with $[a, b] \in F$. The task is to find a cluster point of $F$ in $[a, b]$. Let
$$S = \{x \in [a, b] : [x, b] \in F\}.$$
Then $a \in S$, since $[a, b] \in F$. The set $S$ is bounded above by $b$. By the least upper bound property, $c = \sup S$ exists, and $a \le c \le b$.

The point $c$ is a cluster point of $F$. Suppose not. Since the intervals $(c - \varepsilon, c + \varepsilon)$ form a basis of $\mathcal{N}(c)$, there is an $\varepsilon > 0$ and an $A \in F$ with $A \cap (c - \varepsilon, c + \varepsilon) = \emptyset$. Since $c = \sup S$, there is an $x \in S$ with $x > c - \varepsilon$. Then $[x, b] \in F$, so $B = A \cap [x, b] \in F$. Each $y \in B$ satisfies $y \ge x > c - \varepsilon$ and $y \notin (c - \varepsilon, c + \varepsilon)$, so $y \ge c + \varepsilon$. So $B \subseteq [c + \varepsilon, b]$, and $[c + \varepsilon, b] \in F$.

There are two cases. If $c + \varepsilon \le b$, then $c + \varepsilon \in S$, which contradicts $c = \sup S$. If $c + \varepsilon > b$, then $[c + \varepsilon, b] = \emptyset \in F$, which contradicts the properness of $F$. $\square$

*Remarks.* The proof uses only the order: the least upper bound property and the fact that the intervals around $c$ form a basis of $\mathcal{N}(c)$. So it proves the theorem in each conditionally complete linear order with the order topology. The proof of Mathlib follows the same lines. In $\mathbb{Q}$ the proof fails at the choice of $c$, and the theorem is false: $[0, 2] \cap \mathbb{Q}$ is not compact, since the open cover by the sets $\{q : |q^2 - 2| > 1/n\}$ has no finite subcover.

::: mathlib
`ConditionallyCompleteLinearOrder.toCompactIccSpace` · `Mathlib.Topology.Order.Compact`

The theorem, as an instance: a conditionally complete linear order with the order topology has compact closed intervals.

<?decl ConditionallyCompleteLinearOrder.toCompactIccSpace?>
:::

**Theorem (Compactness by ultrafilters).** A set $K$ is compact if and only if each ultrafilter $U$ with $K \in U$ converges to a point of $K$, that is, $U \le \mathcal{N}(x)$ for some $x \in K$.

*Proof.* Assume $K$ is compact, and let $U$ be an ultrafilter with $K \in U$. By compactness it has a cluster point $x \in K$. A cluster point of an ultrafilter is a limit (Chapter 2), so $U \le \mathcal{N}(x)$.

Conversely, let $F$ be a proper filter with $K \in F$. By the ultrafilter lemma there is an ultrafilter $U \le F$. Then $K \in U$, so $U \le \mathcal{N}(x)$ for some $x \in K$. For $N \in \mathcal{N}(x)$ and $A \in F$, both sets are in $U$, so $N \cap A \in U$ is nonempty. So $x$ is a cluster point of $F$. $\square$

::: mathlib
`isCompact_iff_ultrafilter_le_nhds` · `Mathlib.Topology.Compactness.Compact`

The theorem. In a compact space, `Ultrafilter.le_nhds_lim` gives a chosen limit `F.lim` of each ultrafilter.

<?decl isCompact_iff_ultrafilter_le_nhds?>
:::

::: mathlib
`Ultrafilter.le_nhds_lim` · `Mathlib.Topology.Compactness.Compact`

In a compact space each ultrafilter converges to its chosen limit.

<?decl Ultrafilter.le_nhds_lim?>
:::

**Theorem (Convergence in a product).** Let $F$ be a filter on a set $A$ and $f : A \to \prod_i X_i$. Then $f$ tends to $\mathcal{N}(x)$ along $F$ if and only if each coordinate $\pi_i \circ f$ tends to $\mathcal{N}(x_i)$.

*Proof.* Each $\pi_i$ is continuous, so the direct implication is the composition of limits. Conversely, assume the coordinate limits and let $N$ be a neighbourhood of $x$. It contains a basic set $W = \pi_{i_1}^{-1}(V_1) \cap \dots \cap \pi_{i_n}^{-1}(V_n)$ with $V_k$ an open neighbourhood of $x_{i_k}$. Then $f^{-1}(W) = \bigcap_k (\pi_{i_k} \circ f)^{-1}(V_k)$ is a finite intersection of members of $F$, so it is in $F$, and so is $f^{-1}(N) \supseteq f^{-1}(W)$. $\square$

::: mathlib
`tendsto_pi_nhds` · `Mathlib.Topology.Constructions`

The theorem. It comes from `nhds_pi`, which says that the neighbourhood filter of `a` is the product filter of the filters `𝓝 (a i)`.

<?decl tendsto_pi_nhds?>
:::

::: mathlib
`nhds_pi` · `Mathlib.Topology.Constructions`

The neighbourhood filter in a product is the product of the neighbourhood filters.

<?decl nhds_pi?>
:::

**Theorem (Tychonoff).** Let $(X_i)_{i \in I}$ be spaces and $K_i \subseteq X_i$ compact for each $i$. Then $K = \prod_i K_i$ is compact in $\prod_i X_i$. In particular a product of compact spaces is compact.

*Proof.* By the theorem on ultrafilters, it suffices to show that each ultrafilter $U$ with $K \in U$ converges to a point of $K$. Fix $i$. The image $(\pi_i)_{*}U$ is an ultrafilter on $X_i$ (Chapter 2). It contains $K_i$, since $\pi_i^{-1}(K_i) \supseteq K$ is in $U$. Since $K_i$ is compact, $(\pi_i)_{*}U \le \mathcal{N}(x_i)$ for some $x_i \in K_i$. By the axiom of choice, choose such an $x_i$ for each $i$, and let $x = (x_i)_i \in K$.

The statement $(\pi_i)_{*}U \le \mathcal{N}(x_i)$ says that $\pi_i$ tends to $\mathcal{N}(x_i)$ along $U$. Apply the theorem on convergence in a product to the identity map of $\prod_i X_i$, whose coordinates are the $\pi_i$. It gives that the identity tends to $\mathcal{N}(x)$ along $U$, that is, $U \le \mathcal{N}(x)$. $\square$

*Remarks.* The proof uses the axiom of choice twice: in the ultrafilter lemma and in the choice of the $x_i$. In a product of Hausdorff spaces the second choice is not needed, since the limit $x_i$ is unique. Kelley proved in 1950 that the Tychonoff theorem for arbitrary spaces implies the axiom of choice.

::: mathlib
`isCompact_univ_pi` · `Mathlib.Topology.Compactness.Compact`

The theorem for `Set.univ.pi s`, the product of the sets `s i`. The version `isCompact_pi_infinite` states it for `{x | ∀ i, x i ∈ s i}`. The proof in Mathlib is the ultrafilter proof above.

<?decl isCompact_univ_pi?>
:::

::: mathlib
`isCompact_pi_infinite` · `Mathlib.Topology.Compactness.Compact`

The Tychonoff theorem for a set of functions with values in compact sets.

<?decl isCompact_pi_infinite?>
:::

::: mathlib
`Pi.compactSpace` · `Mathlib.Topology.Compactness.Compact`

A product of compact spaces is a compact space, as an instance.

<?decl Pi.compactSpace?>
:::

::: mathlib
`IsCompact.prod` · `Mathlib.Topology.Compactness.Compact`

The case of two factors: `s ×ˢ t` is compact.

<?decl IsCompact.prod?>
:::

### Examples

**Example (Closed boxes).** By the Tychonoff theorem for finitely many factors, each box $[a_1, b_1] \times \dots \times [a_n, b_n]$ is compact in $\mathbb{R}^n$. A closed subset of a box is compact. Section 3 shows the converse in $\mathbb{R}^n$: a compact set is closed and bounded.

**Example (The Hilbert cube and the Cantor space).** The product $[0, 1]^{\mathbb{N}}$ is compact. So is $\{0, 1\}^{\mathbb{N}}$, with $\{0, 1\}$ discrete. The map $(\varepsilon_n) \mapsto \sum_n 2 \varepsilon_n 3^{-n-1}$ is a continuous injection of $\{0, 1\}^{\mathbb{N}}$ into $[0, 1]$, so a homeomorphism onto its image by the compact to Hausdorff criterion of Section 1. The image is the Cantor set.

**Counterexample (The box topology).** With the box topology, $[0, 1]^{\mathbb{N}}$ is not compact. The sets $\prod_n U_n^{\varepsilon_n}$, where $\varepsilon \in \{0, 1\}^{\mathbb{N}}$, $U^0 = [0, 2/3)$ and $U^1 = (1/3, 1]$, are open in the box topology and cover the space. Each point $(x_n)$ with $x_n \in \{0, 1\}$ lies in exactly one of them, and there are uncountably many such points. So no finite subfamily covers. The Tychonoff theorem is a theorem about the product topology.

### The library around it

The compactness of intervals is in `Mathlib.Topology.Order.Compact`, with the general instance for conditionally complete linear orders. The Tychonoff theorem is in `Mathlib.Topology.Compactness.Compact`, together with the ultrafilter characterisation. The product filter `Filter.pi` is in `Mathlib.Order.Filter.Pi`, and the neighbourhoods in a product are described by `nhds_pi`.

The module `Mathlib.Topology.IsClosedRestrict` studies the restriction of functions on a product to a set of coordinates. For a set $S$ of indices, the restriction $\prod_{i} \alpha_i \to \prod_{i \in S} \alpha_i$ is `S.domRestrict`. If each $\alpha_i$ is compact, this restriction is a closed map, `isClosedMap_restrict_of_compactSpace`. Without compact factors, the image of a compact closed set is still closed, `IsCompact.isClosed_image_restrict`, and the form for one coordinate is `IsClosed.isClosed_image_eval`. For the proof, let $K$ be the image of $s$ in $\prod_{i \notin S} \alpha_i$; it is compact. The homeomorphism `Homeomorph.preimageImageRestrict` identifies the points whose restriction to the complement of $S$ lies in $K$ with the product $K \times \prod_{i \in S} \alpha_i$. The projection of this product onto its second factor is a closed map because $K$ is compact, and the image of $s$ is the projection of a closed subset.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that $[0, 1] \times [0, 1]$ is compact by applying the theorem on images to $[0,1]^{\{1, 2\}}$.
2. (A) Show that the unit circle and the closed unit disc in $\mathbb{R}^2$ are compact.
3. (A) Show directly that $[0, 1] \cap \mathbb{Q}$ is not compact.
4. (B) Adapt the proof of the compactness of $[a, b]$ to show that a linearly ordered set with the order topology in which each nonempty set bounded above has a supremum has compact closed intervals.
5. (B) Show that a set $K \subseteq \prod_i X_i$ is contained in a compact set if and only if each projection $\pi_i(K)$ is contained in a compact set.
6. (B) Give an open cover proof of the compactness of $[a, b]$, with the set of $x$ such that $[a, x]$ has a finite subcover.
7. (C) Prove the Tychonoff theorem for two factors with open covers only, by the tube lemma: if $K$ is compact and $\{y\} \times K \subseteq W$ with $W$ open, then $V \times K \subseteq W$ for some open $V \ni y$.

### Notes and history

Tychonoff proved the theorem in 1930 for products of intervals and in 1935 in general. The proof with ultrafilters is due to Cartan (1937), and it is the proof of Bourbaki. The filter proof of the compactness of $[a, b]$ follows the supremum argument of the Heine-Borel theorem; in Mathlib it is proved in the generality of conditionally complete linear orders, and so it gives the compactness of closed intervals in $\mathbb{R}$, in the extended reals and in each complete lattice with the order topology.

### Reference

<?reference?>
