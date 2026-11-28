---
title: Products, sums, Cayley graphs and other constructions
kind: api
modules:
  - Mathlib.Combinatorics.SimpleGraph.Prod
  - Mathlib.Combinatorics.SimpleGraph.Sum
  - Mathlib.Combinatorics.SimpleGraph.Operations
  - Mathlib.Combinatorics.SimpleGraph.LineGraph
  - Mathlib.Combinatorics.SimpleGraph.Cayley
  - Mathlib.Combinatorics.SimpleGraph.Circulant
  - Mathlib.Combinatorics.SimpleGraph.Hasse
  - Mathlib.Combinatorics.SimpleGraph.Star
  - Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic
  - Mathlib.Combinatorics.SimpleGraph.StronglyRegular
explains:
  E2: [SimpleGraph.degree_boxProd, SimpleGraph.chromaticNumber_sum, SimpleGraph.card_edgeFinset_replaceVertex_of_not_adj, SimpleGraph.mulCayley_adj, SimpleGraph.hasse_prod, SimpleGraph.IsSRGWith.param_eq]
  E1: auto
families: []
requires: [V03.C03, V03.C06, V04.C03, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Products, sums, Cayley graphs and other constructions

### Overview

This section collects the ways in which Mathlib builds new graphs. Some constructions combine two graphs: the box product $G \mathbin{\square} H$ and the disjoint sum $G \oplus H$. Some change a graph in one place: the addition of one edge and the replacement of one vertex by a copy of another. Some turn a graph into another graph: the line graph. The others build a graph from a different structure: the Cayley graph of a group and a set of generators, the circulant graphs, the Hasse diagram of a partial order and the path graphs, the star graphs, and the embeddings of a graph in a metric space with edges of length $1$.

The last module is about one class of graphs: the strongly regular graphs, with the Petersen graph of Section 1 as the standard example.

Some statements use the walks of Chapter 2 and the colourings of Chapter 3. A reader can skip them on a first reading.

### The library around it

#### The box product

The module `Mathlib.Combinatorics.SimpleGraph.Prod` defines the box product, also called the Cartesian product. For graphs $G$ on $\alpha$ and $H$ on $\beta$, the graph `SimpleGraph.boxProd G H`, with the notation `G □ H`, lives on `α × β`. Two pairs are adjacent when they agree in one coordinate and are adjacent in the other:

$$(a_1, b_1) \sim (a_2, b_2) \iff (a_1 \sim_G a_2 \wedge b_1 = b_2) \vee (b_1 \sim_H b_2 \wedge a_1 = a_2).$$

This is `SimpleGraph.boxProd_adj`, and `SimpleGraph.boxProd_adj_left` and `SimpleGraph.boxProd_adj_right` are the two special cases with one equal coordinate. The grid $P_m \mathbin{\square} P_n$ and the hypercube $Q_n = K_2 \mathbin{\square} \cdots \mathbin{\square} K_2$ are box products. The product is commutative and associative up to isomorphism: `SimpleGraph.boxProdComm` and `SimpleGraph.boxProdAssoc` are the isomorphisms `G □ H ≃g H □ G` and `G □ H □ I ≃g G □ (H □ I)`. For each $b$ the map $a \mapsto (a, b)$ is an embedding `SimpleGraph.boxProdLeft G H b : G ↪g G □ H`, and `SimpleGraph.boxProdRight` is the embedding of $H$ at a fixed first coordinate.

**Theorem.** Let $x = (a, b)$ be a vertex of $G \mathbin{\square} H$ with finite neighbour sets. Then $\deg_{G \square H}(x) = \deg_G(a) + \deg_H(b)$.

*Proof.* By the adjacency rule, the neighbours of $x$ are the pairs $(a', b)$ with $a' \sim_G a$ and the pairs $(a, b')$ with $b' \sim_H b$. A pair of the first kind has the second coordinate $b$, and a pair of the second kind has a second coordinate $b' \neq b$, because $H$ has no loop. So the two sets are disjoint, and they have $\deg_G(a)$ and $\deg_H(b)$ elements. $\square$

This is `SimpleGraph.degree_boxProd`. The set form is `SimpleGraph.neighborSet_boxProd`.

A walk in $G \mathbin{\square} H$ moves in one coordinate at each step. `SimpleGraph.Walk.boxProdLeft` lifts a walk of $G$ to the product, and `SimpleGraph.Walk.ofBoxProdLeft` projects a walk of the product to $G$ and keeps only the steps in the first coordinate. The length of a walk is the sum of the lengths of its two projections (`SimpleGraph.Walk.length_boxProd`).

A walk of the product projects to walks of the two factors, and two lifted walks concatenate to a walk of the product. So $(a_2, b_2)$ is reachable from $(a_1, b_1)$ if and only if $a_2$ is reachable from $a_1$ and $b_2$ from $b_1$ (`SimpleGraph.reachable_boxProd`). It gives `SimpleGraph.connected_boxProd`: the product is connected if and only if both factors are connected. The preconnected form of the converse needs a nonempty other factor (`SimpleGraph.Preconnected.ofBoxProdLeft`), because a product with an empty factor has no vertex. The same argument with lengths gives the distance formula $d_{G \square H}(x, y) = d_G(x_1, y_1) + d_H(x_2, y_2)$, which is `SimpleGraph.edist_boxProd` for the extended distance of Chapter 2.

#### The disjoint sum

The module `Mathlib.Combinatorics.SimpleGraph.Sum` defines `SimpleGraph.sum G H`, with the notation `G ⊕g H`, on the sum type `V ⊕ W`. No edge joins the two sides. The adjacency lemmas are `SimpleGraph.sum_adj_inl`, `SimpleGraph.sum_adj_inr` and `SimpleGraph.not_adj_sum_inl_inr`. The isomorphisms `SimpleGraph.Iso.sumComm`, `SimpleGraph.Iso.sumAssoc` and `SimpleGraph.Iso.sumCongr` follow the equivalences of types, and `SimpleGraph.Hom.sum` and `SimpleGraph.Embedding.sum` act on each side. The box product distributes over the sum (`SimpleGraph.Iso.boxProdSumDistrib`).

The sum is never connected when both sides are nonempty: no left vertex reaches a right vertex (`SimpleGraph.not_reachable_sum_inl_inr`, `SimpleGraph.not_connected_sum`). One edge between connected sides repairs this, and `SimpleGraph.Connected.sum_sup_edge` states that `(G ⊕g H) ⊔ edge (Sum.inl v) (Sum.inr w)` is connected.

A colouring of the sum is a pair of colourings, one for each side (`SimpleGraph.Coloring.sumEquiv`).

**Theorem.** $\chi(G \oplus H) = \max(\chi(G), \chi(H))$.

*Proof.* The sum contains copies of $G$ and $H$, so $\chi(G \oplus H) \geq \max(\chi(G), \chi(H))$. Conversely, colour both sides with the same $m = \max(\chi(G), \chi(H))$ colours. No edge joins the sides, so the union is a proper colouring. $\square$

This is `SimpleGraph.chromaticNumber_sum`, in the extended natural numbers of Chapter 3. The finite form is `SimpleGraph.colorable_sum`.

#### Local operations: one edge and one replaced vertex

The module `Mathlib.Combinatorics.SimpleGraph.Operations` has two local operations. The graph `SimpleGraph.edge s t` has the single edge $st$ and nothing else. It is `fromEdgeSet {s(s, t)}`, so `SimpleGraph.edge_self_eq_bot` states that `edge s s` is the empty graph. To add an edge to $G$, write `G ⊔ edge s t`. Then `SimpleGraph.card_edgeFinset_sup_edge` states that the number of edges goes up by one when $s \neq t$ and $s \not\sim t$, and `SimpleGraph.sup_edge_of_adj` states that nothing changes when $s \sim t$.

The graph `G.replaceVertex s t` replaces the vertex $t$ by a copy of $s$. The new neighbours of $t$ are the old neighbours of $s$, the other adjacencies do not change, and the edge $st$ is removed if it is present (`SimpleGraph.not_adj_replaceVertex_same`). This is the step of the symmetrization argument of Zykov, which the proof of Turán's theorem in Mathlib uses.

**Theorem.** Let $G$ be a finite graph and $s \not\sim t$. Then $|E(G.\mathrm{replaceVertex}\ s\ t)| = |E(G)| + \deg(s) - \deg(t)$.

*Proof.* The operation removes the $\deg(t)$ edges at $t$ and adds the $\deg(s)$ edges $xt$ with $x \sim s$. No new edge is the loop $tt$, because $t \not\sim s$. $\square$

This is `SimpleGraph.card_edgeFinset_replaceVertex_of_not_adj`, written as `#G.edgeFinset + G.degree s - G.degree t` in `ℕ`. When $s \sim t$, one more edge is lost, and `SimpleGraph.card_edgeFinset_replaceVertex_of_adj` subtracts $1$.

#### The line graph

The module `Mathlib.Combinatorics.SimpleGraph.LineGraph` defines `G.lineGraph`, a graph on the subtype `↥G.edgeSet` of edges. Two edges are adjacent when they are different and share an end (`SimpleGraph.lineGraph_adj_iff_exists`). A matching of $G$ is an independent set of the line graph, and a proper edge colouring of $G$ is a proper vertex colouring of the line graph. An isomorphism $G \cong G'$ gives an isomorphism of line graphs (`SimpleGraph.Iso.lineGraph`), and a copy of $G$ in $G'$ gives a copy of the line graph (`SimpleGraph.Copy.lineGraph`).

A copy of $G$ in $G'$ is injective on vertices, so two edges of $G$ share an end if and only if their images share an end. So $L(G)$ is an induced subgraph of $L(G')$ when $G$ is contained in $G'$. This is `SimpleGraph.IsContained.isIndContained_lineGraph`, with the embedding `SimpleGraph.Copy.toLineGraphEmbedding`. The containment relations `SimpleGraph.IsContained` and `SimpleGraph.IsIndContained` are those of Section 2.

#### Cayley graphs and circulant graphs

The module `Mathlib.Combinatorics.SimpleGraph.Cayley` defines the Cayley graph `SimpleGraph.mulCayley s` of a set $s$ in a type with a multiplication. It is `fromRel` of the relation $u \cdot g = v$ for some $g \in s$, so it is the symmetric closure with the loops removed. The additive form is `SimpleGraph.addCayley s`, and each lemma has the two forms. In a group the adjacency has a closed form.

**Theorem.** In a group $M$, two elements $u, v$ are adjacent in the Cayley graph of $s$ if and only if $u \neq v$ and $u^{-1} v \in s$ or $v^{-1} u \in s$.

*Proof.* The relation $u g = v$ with $g \in s$ holds if and only if $g = u^{-1} v$ is in $s$. The symmetric closure adds the case $v^{-1} u \in s$, and `fromRel` adds the condition $u \neq v$. $\square$

This is `SimpleGraph.mulCayley_adj`. The graph does not see the identity or the inverses: `SimpleGraph.mulCayley_erase_one` and `SimpleGraph.mulCayley_insert_one` state that removing or adding $1$ does not change the graph, and `SimpleGraph.mulCayley_inv` states that $s$ and $s^{-1}$ give the same graph. The left multiplications act by automorphisms (`SimpleGraph.mulCayley_adj_mul_iff_right`), so a Cayley graph of a group is vertex-transitive and regular. The extreme cases are `SimpleGraph.mulCayley_empty` (the empty graph) and `SimpleGraph.mulCayley_univ` (the complete graph).

The module `Mathlib.Combinatorics.SimpleGraph.Circulant` defines `SimpleGraph.circulantGraph s` for a set $s$ in an additive group, with $a \sim b$ when $a \neq b$ and $a - b \in s$ or $b - a \in s$ (`SimpleGraph.circulantGraph_adj`). The translations act by automorphisms (`SimpleGraph.circulantGraph_adj_translate`), and `SimpleGraph.cycleGraph_eq_circulantGraph` identifies the cycle $C_{n+1}$ with the circulant graph of $\{1\}$.

#### Hasse diagrams and path graphs

The module `Mathlib.Combinatorics.SimpleGraph.Hasse` defines the Hasse diagram `SimpleGraph.hasse α` of a preorder. Two elements are adjacent when one covers the other: `SimpleGraph.hasse_adj` states $a \sim b \iff a \lessdot b \vee b \lessdot a$. The order dual has the same diagram (`SimpleGraph.hasseDualIso`), and the diagram has no triangle (`SimpleGraph.cliqueFree_hasse_three`).

**Theorem.** For partial orders $\alpha$ and $\beta$, the Hasse diagram of $\alpha \times \beta$ is the box product of the Hasse diagrams.

*Proof.* In the product order, $(a_1, b_1) \lessdot (a_2, b_2)$ holds if and only if either $a_1 \lessdot a_2$ and $b_1 = b_2$, or $a_1 = a_2$ and $b_1 \lessdot b_2$. A pair that grows in both coordinates is not a cover, because $(a_2, b_1)$ lies strictly between. $\square$

This is `SimpleGraph.hasse_prod`. With it, the hypercube $Q_n$ is the Hasse diagram of the Boolean lattice of subsets of an $n$-set. The path graph `SimpleGraph.pathGraph n` is defined as the Hasse diagram of `Fin n`, so $i \sim j$ when $i + 1 = j$ or $j + 1 = i$ (`SimpleGraph.pathGraph_adj`). It is connected for $n \geq 1$ (`SimpleGraph.connected_pathGraph`). A walk $w$ of length $\ell$ gives a homomorphism `SimpleGraph.Walk.pathGraphHom` from $P_{\ell + 1}$, and a path gives a copy (`SimpleGraph.Walk.IsPath.pathGraphCopy`). For a linear order with the successor structure of Volume 4, the Hasse diagram is preconnected (`SimpleGraph.preconnected_hasse_of_succOrder`).

#### Star graphs

The module `Mathlib.Combinatorics.SimpleGraph.Star` defines `SimpleGraph.starGraph r`: every vertex other than the centre $r$ is adjacent to $r$, and there is no other edge (`SimpleGraph.starGraph_adj`). With $n$ vertices the centre has degree $n - 1$ and every other vertex has degree $1$ (`SimpleGraph.degree_starGraph_center`, `SimpleGraph.degree_starGraph_of_ne_center`). A graph contains the star at $r$ if and only if $r$ is a universal vertex, adjacent to all others (`SimpleGraph.starGraph_le_iff`).

The star is a tree (`SimpleGraph.isTree_starGraph`): it is connected through $r$, and a cycle would pass through a vertex other than $r$ with two neighbours. A graph with a universal vertex is a forest if and only if it has no triangle (`SimpleGraph.IsUniversal.isAcyclic_iff_cliqueFree_three`), because such a graph with no triangle is the star itself.

#### Unit-distance embeddings

The module `Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic` defines the structure `G.UnitDistEmbedding E` for a metric space $E$. It is an injective map `p : V ↪ E` with `dist (p u) (p v) = 1` for each edge $uv$ (the field `SimpleGraph.UnitDistEmbedding.unit_dist`). Non-adjacent vertices may also be at distance $1$. The module transfers an embedding to a smaller graph: along a copy (`SimpleGraph.UnitDistEmbedding.copy`), along a graph embedding (`SimpleGraph.UnitDistEmbedding.embed`) and along an isomorphism (`SimpleGraph.UnitDistEmbedding.iso`).

#### Strongly regular graphs

The module `Mathlib.Combinatorics.SimpleGraph.StronglyRegular` defines `G.IsSRGWith n k ℓ μ` for a finite graph. It has four fields: $G$ has $n$ vertices (`card`), it is $k$-regular (`regular`), two adjacent vertices have exactly $\ell$ common neighbours (`of_adj`), and two distinct non-adjacent vertices have exactly $\mu$ common neighbours (`of_not_adj`). The Petersen graph is strongly regular with the parameters $(10, 3, 0, 1)$.

**Theorem.** If $G$ is strongly regular with the parameters $(n, k, \ell, \mu)$ and $n > 0$, then $k(k - \ell - 1) = (n - k - 1)\mu$.

*Proof.* Fix a vertex $v$. Count the pairs $(w, x)$ with $w \sim v$, $x \sim w$, $x \neq v$ and $x \not\sim v$. Each of the $k$ neighbours $w$ of $v$ has $k$ neighbours: $v$ itself, $\ell$ common neighbours with $v$, and $k - \ell - 1$ others. So the count is $k(k - \ell - 1)$. On the other side, there are $n - k - 1$ vertices $x \neq v$ with $x \not\sim v$, and each has $\mu$ common neighbours with $v$. So the count is $(n - k - 1)\mu$. $\square$

This is `SimpleGraph.IsSRGWith.param_eq`. The complement of a strongly regular graph is strongly regular with the parameters $(n, n - k - 1, n - 2 - 2k + \mu, n - 2k + \ell)$ (`SimpleGraph.IsSRGWith.compl`), stated in `ℕ` as `n - (2 * k - μ) - 2` and `n - (2 * k - ℓ)`. In the language of the adjacency matrix of Section 2, the definition says $A^2 = kI + \ell A + \mu A'$, where $A'$ is the adjacency matrix of the complement (`SimpleGraph.IsSRGWith.matrix_eq`). A strongly regular graph with $\mu \neq 0$ that is not complete has diameter $2$ (`SimpleGraph.IsSRGWith.ediam_eq_two`).

#### Common errors

1. A learner writes `G □ H` and expects the tensor product, where $(a_1, b_1) \sim (a_2, b_2)$ needs both $a_1 \sim a_2$ and $b_1 \sim b_2$. The notation `□` is the box product only.
2. A learner expects `SimpleGraph.mulCayley s` to need $1 \notin s$ or $s = s^{-1}$. It needs neither: `fromRel` removes the loops and adds the reverse edges. The degree of a vertex in a group is then $|(s \cup s^{-1}) \setminus \{1\}|$, not $|s|$.
3. A learner uses the parameters of `SimpleGraph.IsSRGWith.compl` with the subtraction of the integers. The statement uses the truncated subtraction of `ℕ`, so a rewrite with it needs the bounds $\mu \leq 2k$ and $2k - \mu + 2 \leq n$ at hand, or a cast to `ℤ`.

### Exercises

1. (A) Show that the hypercube $Q_n$ has $2^n$ vertices and $n 2^{n-1}$ edges, from `SimpleGraph.degree_boxProd` and the degree-sum formula.
2. (A) Show that the Cayley graph of $\mathbb{Z}/n$ with $s = \{1\}$ and the circulant graph of $\{1\}$ are the same graph, and that both are the cycle $C_n$ for $n \geq 3$.
3. (A) Compute the number of edges of the line graph of $K_{1,n}$ and of $K_4$. Show that the line graph of the star $K_{1,n}$ is $K_n$.
4. (B) Show that the grid $P_m \mathbin{\square} P_n$ with $m, n \geq 2$ is bipartite, and give the distance between two vertices with `SimpleGraph.edist_boxProd`.
5. (B) Show that $K_{3,3}$ is strongly regular, find its parameters and check `SimpleGraph.IsSRGWith.param_eq`. Then find the parameters of its complement.
6. (C) Let $G$ be strongly regular with the parameters $(n, k, \ell, \mu)$, $\mu > 0$. From $A^2 = kI + \ell A + \mu(J - I - A)$, show that the eigenvalues of $A$ other than $k$ are the two roots of $x^2 - (\ell - \mu)x - (k - \mu) = 0$. Compute them for the Petersen graph.

### Reference

<?reference?>
