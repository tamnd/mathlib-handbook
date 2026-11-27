---
title: Regularity, triangle removal and Roth
kind: theory
modules:
  - Mathlib.Combinatorics.SimpleGraph.Density
  - Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
  - Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
  - Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
  - Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
  - Mathlib.Combinatorics.Additive.AP.Three.Defs
  - Mathlib.Combinatorics.Additive.AP.Three.Behrend
  - Mathlib.Combinatorics.Additive.Corner.Defs
  - Mathlib.Combinatorics.Additive.Corner.Roth
explains:
  E3: [SimpleGraph.edgeDensity, SimpleGraph.IsUniform, Finpartition.IsUniform, szemeredi_regularity, SimpleGraph.FarFromTriangleFree, SimpleGraph.triangle_removal, ThreeAPFree, rothNumberNat, IsCorner, IsCornerFree, corners_theorem, roth_3ap_theorem, rothNumberNat_isLittleO_id, Behrend.roth_lower_bound]
  E2: [SimpleGraph.interedges, SimpleGraph.edgeDensity_def, SimpleGraph.card_interedges_div_card, SimpleGraph.edgeDensity_le_one, SimpleGraph.edgeDensity_nonneg, SimpleGraph.edgeDensity_comm, SimpleGraph.edgeDensity_add_edgeDensity_compl, Rel.edgeDensity, Rel.interedges, SimpleGraph.not_isUniform_iff, SimpleGraph.IsUniform.symm, SimpleGraph.IsUniform.mono, SimpleGraph.isUniform_comm, SimpleGraph.isUniform_one, SimpleGraph.nonuniformWitnesses, Finpartition.nonUniforms, Finpartition.bot_isUniform, Finpartition.sparsePairs, SimpleGraph.regularityReduced, SimpleGraph.triangleRemovalBound, SimpleGraph.triangleRemovalBound_pos, SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset, ThreeGPFree, threeAPFree_empty, threeAPFree_singleton, ThreeAPFree.mono, threeAPFree_iff_eq_right, addRothNumber, rothNumberNat_def, rothNumberNat_le, rothNumberNat_add_le, ThreeAPFree.le_rothNumberNat, isCorner_iff, isCornerFree_iff, IsCornerFree.mono, cornersTheoremBound, corners_theorem_nat, roth_3ap_theorem_nat, threeAPFree_sphere, Behrend.box, Behrend.sphere, Behrend.threeAPFree_sphere, Behrend.threeAPFree_image_sphere, Behrend.exists_large_sphere, Behrend.card_sphere_le_rothNumberNat, Behrend.roth_lower_bound_explicit]
  E1: auto
families: []
requires: [V30.C01, V30.C03, V03.C03, V03.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Regularity, triangle removal and Roth

### Overview

A set of integers with no three-term arithmetic progression cannot be dense. This is the theorem of Roth from 1953: if $r(N)$ is the largest size of a subset of $\{0, \dots, N - 1\}$ with no progression $a, a + d, a + 2d$ with $d \neq 0$, then $r(N)/N \to 0$. Roth proved it with Fourier analysis. This section gives the graph-theoretic proof of Ruzsa and Szemerédi from 1978, which is the proof in Mathlib.

The proof has three steps. The regularity lemma of Szemerédi says that each large graph is close to a union of a bounded number of random-like bipartite graphs. The triangle removal lemma follows from it: a graph with few triangles can be made triangle-free by the deletion of few edges. The corners theorem and then the theorem of Roth follow from the removal lemma, applied to a graph that has one triangle for each point of the set and one more triangle for each corner. The section ends with the construction of Behrend from 1946, which shows that $r(N)$ is not much smaller than $N$: $r(N) \ge N e^{-4\sqrt{\log N}}$.

This section proves the counting lemma, the removal lemma from the regularity lemma, the corners theorem, the theorem of Roth and the bound of Behrend. It states the regularity lemma and outlines its proof.

### Definitions

In this section, $G$ is a finite graph on a set $V$ with $n$ vertices. For finite $X, Y \subseteq V$, $e(X, Y)$ is the number of pairs $(x, y) \in X \times Y$ with $x \sim y$.

**Definition (Edge density).** For non-empty $X, Y$, the edge density is $d(X, Y) = e(X, Y)/(|X||Y|)$, a number in $[0, 1]$.

::: mathlib
`SimpleGraph.edgeDensity` · `Mathlib.Combinatorics.SimpleGraph.Density`

`G.edgeDensity s t : ℚ` is `#(G.interedges s t) / (#s * #t)`, where `SimpleGraph.interedges` is the finset of pairs in `s ×ˢ t` that are adjacent. The unfolding is `SimpleGraph.edgeDensity_def`. The density is in $[0, 1]$ by `SimpleGraph.edgeDensity_nonneg` and `SimpleGraph.edgeDensity_le_one`, it is symmetric by `SimpleGraph.edgeDensity_comm`, and the densities of a graph and its complement add to $1$ on disjoint sets, `SimpleGraph.edgeDensity_add_edgeDensity_compl`. The file defines the same notions for an arbitrary relation as `Rel.interedges` and `Rel.edgeDensity`.

<?decl SimpleGraph.edgeDensity?>
:::

**Definition (Uniform pair).** Let $\varepsilon > 0$. A pair $(X, Y)$ is $\varepsilon$-uniform when for all $X' \subseteq X$ and $Y' \subseteq Y$ with $|X'| \ge \varepsilon |X|$ and $|Y'| \ge \varepsilon |Y|$,
$$|d(X', Y') - d(X, Y)| < \varepsilon.$$

A random bipartite graph with edge probability $p$ between large sets is $\varepsilon$-uniform with high probability, with density close to $p$. Thus a uniform pair behaves like a random graph for counts of small subgraphs.

**Definition (Uniform partition).** A partition $P$ of $V$ into $k$ parts is $\varepsilon$-uniform when at most $\varepsilon k(k - 1)$ of the ordered pairs $(X, Y)$ of distinct parts are not $\varepsilon$-uniform. It is an equipartition when the sizes of two parts differ by at most $1$.

::: mathlib
`SimpleGraph.IsUniform` · `Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform`

`G.IsUniform ε s t` is the condition above, with `#s * ε ≤ #s'` and `#t * ε ≤ #t'` and a strict inequality for the densities, in a linearly ordered field `𝕜`. It is symmetric, `SimpleGraph.IsUniform.symm`, and every pair is `1`-uniform, `SimpleGraph.isUniform_one`. When a pair is not uniform, `SimpleGraph.nonuniformWitnesses` gives the two subsets that show it, with the properties that `SimpleGraph.not_isUniform_iff` describes.

<?decl SimpleGraph.IsUniform?>
:::

::: mathlib
`Finpartition.IsUniform` · `Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform`

`P.IsUniform G ε` for `P : Finpartition A` says `#(P.nonUniforms G ε) ≤ (#P.parts * (#P.parts - 1)) * ε`, where `Finpartition.nonUniforms` is the finset of ordered pairs of distinct parts that are not uniform. The trivial partition is uniform, `Finpartition.bot_isUniform`. The file also defines `Finpartition.sparsePairs` and the reduced graph `SimpleGraph.regularityReduced`, which keeps the edges between parts that form uniform and dense pairs. The proof of the removal lemma uses this graph.

<?decl Finpartition.IsUniform?>
:::

**Definition (Far from triangle-free).** Let $\varepsilon > 0$. The graph $G$ is $\varepsilon$-far from triangle-free when each triangle-free subgraph of $G$ has at most $|E(G)| - \varepsilon n^2$ edges, that is, at least $\varepsilon n^2$ edges must be deleted to destroy all triangles.

::: mathlib
`SimpleGraph.FarFromTriangleFree` · `Mathlib.Combinatorics.SimpleGraph.Triangle.Basic`

`G.FarFromTriangleFree ε` is `G.DeleteFar (fun H ↦ H.CliqueFree 3) (ε * (card α ^ 2 : ℕ))`. The predicate `SimpleGraph.DeleteFar p r` says that each subgraph satisfying `p` is obtained by the deletion of at least `r` edges.

<?decl SimpleGraph.FarFromTriangleFree?>
:::

**Definition (Progression-free set, Roth number).** A subset $A$ of an abelian group is 3AP-free when $a + c = 2b$ with $a, b, c \in A$ implies $a = b$. The Roth number $r(N)$ is the largest size of a 3AP-free subset of $\{0, \dots, N - 1\}$.

The condition $a = b$ forces $c = b$ in a group without elements of order $2$. Thus a 3AP-free set is a set with no progression $a, b, c$ of three distinct terms.

::: mathlib
`ThreeAPFree` · `Mathlib.Combinatorics.Additive.AP.Three.Defs`

`ThreeAPFree s` for `s : Set α` in an additive monoid is `∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a + c = b + b → a = b`. The multiplicative form is `ThreeGPFree`, for geometric progressions. The empty set and the singletons are 3AP-free, `threeAPFree_empty` and `threeAPFree_singleton`, and a subset of a 3AP-free set is 3AP-free, `ThreeAPFree.mono`.

<?decl ThreeAPFree?>
:::

::: mathlib
`rothNumberNat` · `Mathlib.Combinatorics.Additive.AP.Three.Defs`

`rothNumberNat : ℕ →o ℕ` is a monotone function, with `rothNumberNat N = addRothNumber (range N)` by `rothNumberNat_def`. Here `addRothNumber s` is the largest size of a 3AP-free subset of a finset `s`. The basic bounds are `rothNumberNat_le`, `rothNumberNat N ≤ N`, the subadditivity `rothNumberNat_add_le`, and `ThreeAPFree.le_rothNumberNat` for a lower bound from a given set.

<?decl rothNumberNat?>
:::

**Definition (Corner).** Let $G$ be an abelian group and $A \subseteq G \times G$. A corner in $A$ is a triple of points $(x, y)$, $(x, y + d)$, $(x + d, y)$ in $A$. It is trivial when $d = 0$. The set $A$ is corner-free when each corner in $A$ is trivial.

::: mathlib
`IsCorner` · `Mathlib.Combinatorics.Additive.Corner.Defs`

`IsCorner A x₁ y₁ x₂ y₂` is a structure with the fields `(x₁, y₁) ∈ A`, `(x₁, y₂) ∈ A`, `(x₂, y₁) ∈ A` and `x₁ + y₂ = x₂ + y₁`. The last condition says $y_2 - y_1 = x_2 - x_1$, but it is written without subtraction, so the definition makes sense in a commutative monoid such as `ℕ`. The unfolding is `isCorner_iff`.

<?decl IsCorner?>
:::

::: mathlib
`IsCornerFree` · `Mathlib.Combinatorics.Additive.Corner.Defs`

`IsCornerFree A` is `∀ ⦃x₁ y₁ x₂ y₂⦄, IsCorner A x₁ y₁ x₂ y₂ → x₁ = x₂`. When `A ⊆ s ×ˢ s`, `isCornerFree_iff` restricts the quantifiers to `s`.

<?decl IsCornerFree?>
:::

### Theorems and proofs

**Theorem (Szemerédi regularity lemma).** For each $\varepsilon > 0$ and $l \ge 1$, there is $M = M(\varepsilon, l)$ such that each graph with at least $l$ vertices has an $\varepsilon$-uniform equipartition into $k$ parts with $l \le k \le M$.

*Outline of the proof.* For a partition $P = \{V_1, \dots, V_k\}$, define the index
$$q(P) = \sum_{i, j} \frac{|V_i||V_j|}{n^2}\, d(V_i, V_j)^2,$$
a number in $[0, 1]$. It is the mean square of the density over a random pair of vertices. By the Cauchy-Schwarz inequality, $q$ does not decrease when $P$ is refined. If the pair $(V_i, V_j)$ is not $\varepsilon$-uniform, the witnesses $X' \subseteq V_i$ and $Y' \subseteq V_j$ split the two parts, and the split increases the contribution of the pair to $q$ by at least $\varepsilon^4 |V_i||V_j|/n^2$. If $P$ is not $\varepsilon$-uniform, refine all parts at the same time by all witnesses, and then make the result an equipartition again. The index increases by at least about $\varepsilon^5/2$. Since $q \le 1$, at most about $2\varepsilon^{-5}$ steps are possible. Each step increases the number of parts at most exponentially, so $M$ is a tower of twos of height about $\varepsilon^{-5}$. $\square$

The tower bound is necessary. Gowers proved in 1997 that some graphs need a number of parts that is a tower of height polynomial in $1/\varepsilon$.

::: mathlib
`szemeredi_regularity` · `Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma`

`szemeredi_regularity (G : SimpleGraph α) (hε : 0 < ε) (hl : l ≤ card α) : ∃ P : Finpartition univ, P.IsEquipartition ∧ l ≤ #P.parts ∧ #P.parts ≤ SzemerediRegularity.bound ε l ∧ P.IsUniform G ε`. The bound is an explicit function, defined in `Mathlib.Combinatorics.SimpleGraph.Regularity.Bound`. The proof is split over the files of the folder: the index is in `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy`, the refinement of one part is in `Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk`, and one step of the increment is in `Mathlib.Combinatorics.SimpleGraph.Regularity.Increment`. The formal proof follows the proof above closely, and it is one of the larger formal proofs in combinatorics.

<?decl szemeredi_regularity?>
:::

**Lemma (Triangle counting lemma).** Let $X, Y, Z$ be disjoint sets of vertices, let $0 < \varepsilon \le 1/2$, and suppose that the three pairs $(X, Y)$, $(X, Z)$ and $(Y, Z)$ are $\varepsilon$-uniform with densities $d_1 = d(X, Y)$, $d_2 = d(X, Z)$ and $d_3 = d(Y, Z)$, all at least $2\varepsilon$. Then the number of triangles $xyz$ with $x \in X$, $y \in Y$, $z \in Z$ is at least
$$(1 - 2\varepsilon)(d_1 - \varepsilon)(d_2 - \varepsilon)(d_3 - \varepsilon)\,|X||Y||Z|.$$

*Proof.* Let $X_1 \subseteq X$ be the set of $x$ with fewer than $(d_1 - \varepsilon)|Y|$ neighbours in $Y$. Then $d(X_1, Y) < d_1 - \varepsilon$. If $|X_1| \ge \varepsilon |X|$, this contradicts the uniformity of $(X, Y)$ with $Y' = Y$. Thus $|X_1| < \varepsilon |X|$. In the same way, fewer than $\varepsilon|X|$ vertices of $X$ have fewer than $(d_2 - \varepsilon)|Z|$ neighbours in $Z$.

Thus at least $(1 - 2\varepsilon)|X|$ vertices $x \in X$ have a set $N_Y(x)$ of at least $(d_1 - \varepsilon)|Y| \ge \varepsilon|Y|$ neighbours in $Y$, and a set $N_Z(x)$ of at least $(d_2 - \varepsilon)|Z| \ge \varepsilon |Z|$ neighbours in $Z$. By the uniformity of $(Y, Z)$, $d(N_Y(x), N_Z(x)) > d_3 - \varepsilon$. Each edge between $N_Y(x)$ and $N_Z(x)$ makes a triangle with $x$. Thus $x$ is in more than $(d_3 - \varepsilon)(d_1 - \varepsilon)(d_2 - \varepsilon)|Y||Z|$ triangles of this kind. Add over these $x$. $\square$

**Theorem (Triangle removal lemma).** For each $\varepsilon > 0$ there is $\delta > 0$ such that each graph on $n$ vertices with fewer than $\delta n^3$ triangles can be made triangle-free by the deletion of fewer than $\varepsilon n^2$ edges.

*Proof.* Let $\varepsilon \le 1$ and apply the regularity lemma with $\varepsilon/4$ and $l = \lceil 4/\varepsilon \rceil$. The result is an equipartition $V_1, \dots, V_k$ with $l \le k \le M$, where $M$ depends only on $\varepsilon$. For simplicity of the computation, suppose that $k$ divides $n$, so each part has $n/k$ vertices. The general case changes only the constants. Delete these edges:

1. the edges inside a part. There are at most $k (n/k)^2 / 2 = n^2/(2k) \le \varepsilon n^2/8$ of them.
2. the edges between the two parts of a pair that is not $\varepsilon/4$-uniform. There are at most $(\varepsilon/4)k^2$ such pairs, with at most $(n/k)^2$ edges each, so at most $\varepsilon n^2/4$ edges.
3. the edges between the two parts of a pair with density less than $\varepsilon/2$. These are at most $(\varepsilon/2) \cdot n^2/2 = \varepsilon n^2/4$ edges.

In total, fewer than $\varepsilon n^2$ edges are deleted. Suppose that the result $G'$ still has a triangle $xyz$. By step 1, the three vertices are in three different parts $X$, $Y$, $Z$. By steps 2 and 3, the three pairs are $\varepsilon/4$-uniform in $G$ with density at least $\varepsilon/2$. The counting lemma with $\varepsilon/4$ gives at least
$$\Big(1 - \frac{\varepsilon}{2}\Big)\Big(\frac{\varepsilon}{4}\Big)^3 \Big(\frac{n}{k}\Big)^3 \ge \frac{\varepsilon^3}{128 M^3}\, n^3$$
triangles in $G$. Thus $\delta = \varepsilon^3/(128 M^3)$ works: a graph with fewer than $\delta n^3$ triangles cannot keep a triangle after the deletion. $\square$

::: mathlib
`SimpleGraph.triangle_removal` · `Mathlib.Combinatorics.SimpleGraph.Triangle.Removal`

`triangle_removal (hG : #(G.cliqueFinset 3) < triangleRemovalBound ε * card α ^ 3) : ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj, #G.edgeFinset - #G'.edgeFinset < ε * (card α ^ 2 : ℕ) ∧ G'.CliqueFree 3`. The constant `SimpleGraph.triangleRemovalBound ε` is explicit, and it is positive for `0 < ε` by `SimpleGraph.triangleRemovalBound_pos`. The contrapositive form is `SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset`: a graph that is `ε`-far from triangle-free has at least `triangleRemovalBound ε * card α ^ 3` triangles. The proof uses the reduced graph `SimpleGraph.regularityReduced` for the three deletions.

<?decl SimpleGraph.triangle_removal?>
:::

**Theorem (Corners theorem).** For each $\varepsilon > 0$ there is $N_0$ such that, for each finite abelian group $G$ with $|G| = N \ge N_0$, each $A \subseteq G \times G$ with $|A| \ge \varepsilon N^2$ has a non-trivial corner.

*Proof.* Let $A$ be corner-free. Build a tripartite graph $\Gamma$ with three copies $X$, $Y$, $S$ of $G$ as parts, so $\Gamma$ has $3N$ vertices. The vertex $x \in X$ stands for the vertical line $\{x\} \times G$, the vertex $y \in Y$ for the horizontal line $G \times \{y\}$, and the vertex $s \in S$ for the diagonal line $\{(u, v) : u + v = s\}$. Join two vertices when the two lines meet in a point of $A$:
$$x \sim y \iff (x, y) \in A, \qquad y \sim s \iff (s - y, y) \in A, \qquad x \sim s \iff (x, s - x) \in A.$$
A triangle $x, y, s$ gives three points $(x, y)$, $(s - y, y)$, $(x, s - x)$ of $A$. With $d = s - x - y$, these are $(x, y)$, $(x + d, y)$ and $(x, y + d)$, a corner. Thus each triangle has $d = 0$, that is, $s = x + y$, and the triangles correspond to the points of $A$. There are exactly $|A| \le N^2$ triangles.

These triangles are edge-disjoint, because each edge of $\Gamma$ determines its point of $A$, and the point determines the triangle. To destroy all of them, at least one edge of each must be deleted, so at least $|A|$ edges. Now apply the removal lemma with $\varepsilon/9$ and its constant $\delta$. If $N^2 < \delta (3N)^3$, that is, if $N > 1/(27\delta)$, the graph has fewer than $\delta (3N)^3$ triangles. Then fewer than $(\varepsilon/9)(3N)^2 = \varepsilon N^2$ deletions destroy all triangles. Thus $|A| < \varepsilon N^2$. $\square$

::: mathlib
`corners_theorem` · `Mathlib.Combinatorics.Additive.Corner.Roth`

`corners_theorem (ε : ℝ) (hε : 0 < ε) (hG : cornersTheoremBound ε ≤ card G) (A : Finset (G × G)) (hAε : ε * card G ^ 2 ≤ #A) : ¬IsCornerFree (A : Set (G × G))`. The bound `cornersTheoremBound ε` is `⌊(triangleRemovalBound (ε / 9) * 27)⁻¹⌋₊ + 1`, exactly the value $1/(27\delta)$ of the proof above. The graph of the proof is built in `Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite`. The version for subsets of `range n ×ˢ range n` in `ℕ × ℕ` is `corners_theorem_nat`.

<?decl corners_theorem?>
:::

**Theorem (Roth).** For each $\varepsilon > 0$ there is $N_0$ such that, for each finite abelian group $G$ with $|G| = N \ge N_0$, each $A \subseteq G$ with $|A| \ge \varepsilon N$ is not 3AP-free. Also, $r(N)/N \to 0$.

*Proof.* Let $A \subseteq G$ be 3AP-free, and let $B = \{(x, y) \in G \times G : x - y \in A\}$. For each $a \in A$ and $y \in G$, the point $(y + a, y)$ is in $B$, so $|B| = N|A|$. Let $(x, y)$, $(x + d, y)$, $(x, y + d)$ be a corner in $B$. Then $a = x - y$, $a + d$ and $a - d$ are in $A$, and $(a - d) + (a + d) = 2a$. Since $A$ is 3AP-free, $a - d = a$, so $d = 0$. Thus $B$ is corner-free, and the corners theorem gives $N|A| = |B| < \varepsilon N^2$ for $N \ge N_0$. Thus $|A| < \varepsilon N$.

For the integers, let $A \subseteq \{0, \dots, N - 1\}$ be 3AP-free. View $A$ inside $\mathbb{Z}/2N\mathbb{Z}$. If $a + c \equiv 2b \pmod{2N}$ with $a, b, c < N$, then $a + c = 2b$ in $\mathbb{Z}$, because both sides are less than $2N$. Thus $A$ is 3AP-free in $\mathbb{Z}/2N\mathbb{Z}$. By the first part with $\varepsilon/2$, $|A| < (\varepsilon/2) \cdot 2N = \varepsilon N$ for $N$ large. $\square$

::: mathlib
`roth_3ap_theorem` · `Mathlib.Combinatorics.Additive.Corner.Roth`

`roth_3ap_theorem (ε : ℝ) (hε : 0 < ε) (hG : cornersTheoremBound ε ≤ card G) (A : Finset G) (hAε : ε * card G ≤ #A) : ¬ThreeAPFree (A : Set G)`, for a finite abelian group `G`. The integer form is `roth_3ap_theorem_nat`, with `cornersTheoremBound (ε / 3) ≤ n` and `A ⊆ range n`. Mathlib embeds the range in `Fin (2 * n + 1)`, a group of order $2n + 1$, so its constant is $\varepsilon/3$ and not $\varepsilon/2$.

<?decl roth_3ap_theorem?>
:::

::: mathlib
`rothNumberNat_isLittleO_id` · `Mathlib.Combinatorics.Additive.Corner.Roth`

`rothNumberNat_isLittleO_id : (fun N ↦ (rothNumberNat N : ℝ)) =o[atTop] fun N ↦ (N : ℝ)`. This is the statement $r(N) = o(N)$, with the little-o of Volume 15.

<?decl rothNumberNat_isLittleO_id?>
:::

**Theorem (Behrend).** For each $N \ge 1$, $r(N) \ge N e^{-4\sqrt{\log N}}$.

*Proof.* *Spheres are progression-free.* Let $x, y, z \in \mathbb{R}^m$ with $\|x\| = \|y\| = \|z\|$ in the Euclidean norm and $x + z = 2y$. Then $y$ is the midpoint of $x$ and $z$. If $x \neq z$, the strict triangle inequality gives $\|y\| = \|x + z\|/2 < (\|x\| + \|z\|)/2 = \|y\|$, which is false. Thus $x = z$, and then $y = x$.

*From vectors to integers.* Let $d, m \ge 1$, and let the box be $\{0, \dots, d - 1\}^m$. Define $\phi(x) = \sum_{i < m} x_i (2d - 1)^i$, which reads $x$ as the digits of a number in base $2d - 1$. For $x, y, z$ in the box, the digits of $x + z$ and of $2y$ are less than $2d - 1$, so the additions have no carries. Thus $\phi(x) + \phi(z) = 2\phi(y)$ implies $x + z = 2y$ coordinatewise. The map $\phi$ is injective, and its values are less than $(2d - 1)^m$.

*Counting.* For an integer $k$, the sphere $S_k$ is the set of $x$ in the box with $\sum_i x_i^2 = k$. The value $k$ is between $0$ and $m(d - 1)^2 < md^2$, and the box has $d^m$ points. By the pigeonhole principle, some sphere has at least $d^m/(md^2)$ points. Its image under $\phi$ is a 3AP-free subset of $\{0, \dots, (2d - 1)^m - 1\}$, by the first two steps. Thus
$$r\big((2d - 1)^m\big) \ge \frac{d^m}{m d^2}.$$

*Choice of the parameters.* Let $m = \lceil \sqrt{\log N} \rceil$ and choose $d$ as large as possible with $(2d - 1)^m \le N$, so $d$ is about $N^{1/m}/2$. Then $d^m/(md^2)$ is about $N / (2^m m N^{2/m})$. Since $m \approx \sqrt{\log N}$, both $2^m$ and $N^{2/m} = e^{2 \log N / m}$ are at most $e^{c\sqrt{\log N}}$ for constants $c$. A careful computation gives the constant $4$ in the exponent. $\square$

::: mathlib
`Behrend.roth_lower_bound` · `Mathlib.Combinatorics.Additive.AP.Three.Behrend`

`Behrend.roth_lower_bound : N * exp (-4 * √(log N)) ≤ rothNumberNat N`, as reals. The strict form for `4096 ≤ N` is `Behrend.roth_lower_bound_explicit`. The steps of the proof above have names: `threeAPFree_sphere` for a strictly convex normed space, `Behrend.box` and `Behrend.sphere` for the finsets, `Behrend.threeAPFree_sphere` and `Behrend.threeAPFree_image_sphere` for the first two steps, `Behrend.exists_large_sphere` for the pigeonhole step, and `Behrend.card_sphere_le_rothNumberNat` for the bound on $r((2d - 1)^m)$.

<?decl Behrend.roth_lower_bound?>
:::

### Examples

**Example (Small Roth numbers).** The set $\{0, 1, 3, 4\}$ is 3AP-free, and each $5$-element subset of $\{0, \dots, 7\}$ has a 3AP: the values are $r(1), \dots, r(9) = 1, 2, 2, 3, 4, 4, 4, 4, 5$. The greedy set $\{0, 1, 3, 4, 9, 10, 12, 13, \dots\}$ of the integers with no digit $2$ in base $3$ is 3AP-free, and it has $2^j$ elements below $3^j$. This gives $r(N) \ge N^{\log 2/\log 3} \approx N^{0.63}$, much less than the bound of Behrend.

**Example (A uniform pair).** Let $X = Y = \{0, 1\}^3$ and join $x \in X$ to $y \in Y$ when $\sum_i x_i y_i$ is even. The zero vector is joined to all $8$ vertices and each other vector to $4$, so $d(X, Y) = 36/64 = 9/16$. For $X' = \{x : x_1 = 0\}$ and $Y' = \{y : y_2 = 0, y_3 = 0\}$, the density is $1$, because then $\sum_i x_i y_i = 0$. Thus the pair is not $\varepsilon$-uniform for $\varepsilon \le 1/4$. For each fixed $\varepsilon > 0$ and large $m$, the same graph on $\{0, 1\}^m$ is $\varepsilon$-uniform, by the orthogonality of the characters of $(\mathbb{Z}/2\mathbb{Z})^m$.

**Example (The tripartite graph of a corner).** Let $G = \mathbb{Z}/3\mathbb{Z}$ and $A = \{(0, 0), (1, 0), (0, 1)\}$, a corner with $d = 1$. In the graph of the proof, the triangle $x = 0$, $y = 0$, $s = 1$ uses the points $(0, 0)$, $(1, 0)$ and $(0, 1)$. It is a triangle with $s \neq x + y$, the sign of a non-trivial corner.

### The library around it

`Mathlib.Combinatorics.SimpleGraph.Density` has the densities. The folder `Mathlib/Combinatorics/SimpleGraph/Regularity` has uniformity in `Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform`, the lemma in `Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma`, and the parts of the proof in the other files. The folder `Mathlib/Combinatorics/SimpleGraph/Triangle` has the triangle-free graphs and the predicate `SimpleGraph.FarFromTriangleFree` in `Mathlib.Combinatorics.SimpleGraph.Triangle.Basic`, the counting lemma in `Mathlib.Combinatorics.SimpleGraph.Triangle.Counting`, the removal lemma in `Mathlib.Combinatorics.SimpleGraph.Triangle.Removal`, and the tripartite construction in `Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite`. The additive side is in `Mathlib/Combinatorics/Additive/AP/Three` and `Mathlib/Combinatorics/Additive/Corner`. The index of this edition has no declaration for the theorem of Szemerédi on longer progressions, no declaration for the hypergraph removal lemma, and no declaration for the recent bounds of Kelley and Meka, $r(N) \le N e^{-c (\log N)^{1/12}}$.

Common errors of a learner:

- `G.IsUniform ε s t` asks for `#s * ε ≤ #s'`, with the size of the large set on the left. The order of the factors matters when a proof uses `le_div_iff₀`.
- `ThreeAPFree s` concludes `a = b`, not `a = b ∧ b = c`. In `ℕ` and in groups without elements of order $2$, the second equality follows, but in `ZMod 2` it does not.
- `rothNumberNat N` counts subsets of `range N`, that is, of $\{0, \dots, N - 1\}$, not of $\{1, \dots, N\}$. The two numbers are equal by translation, but the Lean statements differ.
- The constants `triangleRemovalBound` and `cornersTheoremBound` are extremely small and large, respectively, because they come from a tower bound. They are not meant for computation.

### Exercises

1. (A) Show that $\{0, 1, 3, 4, 9, 10, 12, 13\}$ is 3AP-free, and find a 3AP-free subset of $\{0, \dots, 8\}$ with $5$ elements.
2. (A) Show that each pair is $\varepsilon$-uniform for $\varepsilon \ge 1$. Show that the complete and the empty bipartite graphs between $X$ and $Y$ give $\varepsilon$-uniform pairs for each $\varepsilon > 0$.
3. (A) Show that $r(M + N) \le r(M) + r(N)$.
4. (B) Show without the removal lemma that a graph on $n$ vertices that is $\varepsilon$-far from triangle-free has at least $\varepsilon n^2/3$ edge-disjoint triangles. Hint: take a maximal family of edge-disjoint triangles and delete all their edges.
5. (B) Deduce from the corners theorem that each dense subset of $\{0, \dots, N - 1\}^2$ contains a corner, with the constant $\varepsilon/9$ of `corners_theorem_nat`. Explain where the factor comes from.
6. (B) Use the removal lemma to show that a graph on $n$ vertices in which each edge is in exactly one triangle has $o(n^2)$ edges. This is the $(6, 3)$-theorem of Ruzsa and Szemerédi.
7. (B) Let $A \subseteq \{1, \dots, n\}$ be 3AP-free. Build a tripartite graph with parts $\{1, \dots, n\}$, $\{1, \dots, 2n\}$ and $\{1, \dots, 3n\}$ and the triangles $(x, x + a, x + 2a)$ for $a \in A$. Show that each edge is in exactly one triangle. With the bound of Behrend, deduce that the function $o(n^2)$ of Exercise 6 cannot be replaced by $n^{2 - c}$ for any $c > 0$.
8. (C) Prove the regularity lemma in full, following the outline. Compute an explicit bound $M(\varepsilon, l)$.
9. (C) Show that a 3AP-free subset of $(\mathbb{Z}/3\mathbb{Z})^m$ has density $o(1)$, with the corners method. Compare with the bound $2.756^m$ of Ellenberg and Gijswijt, which the index of this edition does not have.

### Notes and history

Erdős and Turán asked in 1936 whether dense sets of integers contain long arithmetic progressions. Behrend gave his construction in 1946. Roth proved the case of length three in 1953 with Fourier analysis, and Szemerédi proved the general case in 1975 with a combinatorial argument that contained the first form of the regularity lemma. The graph form of the lemma is from 1978. Ruzsa and Szemerédi proved the $(6, 3)$-theorem in 1978, which contains the removal lemma and the deduction of Roth in this section. The corners theorem is due to Ajtai and Szemerédi in 1974, and Solymosi found the short deduction from the removal lemma in 2003. In 2023, Kelley and Meka proved an upper bound for $r(N)$ that is close to the lower bound of Behrend. The formal proof of the regularity lemma by Dillies and Mehta was published in 2022. The headers list Yaël Dillies and Bhavik Mehta for all the modules of this section.

### Reference

<?reference?>
