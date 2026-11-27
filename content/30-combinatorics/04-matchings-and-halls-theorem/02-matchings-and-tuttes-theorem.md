---
title: Matchings and Tutte's theorem
kind: theory
modules:
  - Mathlib.Combinatorics.SimpleGraph.Matching
  - Mathlib.Combinatorics.SimpleGraph.Hall
  - Mathlib.Combinatorics.SimpleGraph.Tutte
  - Mathlib.Combinatorics.SimpleGraph.VertexCover
  - Mathlib.Combinatorics.SimpleGraph.UniversalVerts
explains:
  E3: [SimpleGraph.Subgraph.IsMatching, SimpleGraph.Subgraph.IsPerfectMatching, SimpleGraph.exists_isMatching_of_forall_ncard_le, SimpleGraph.IsVertexCover, SimpleGraph.vertexCoverNum, SimpleGraph.IsTutteViolator, SimpleGraph.tutte]
  E2: [SimpleGraph.Subgraph.isPerfectMatching_iff, SimpleGraph.Subgraph.isMatching_iff_forall_degree, SimpleGraph.Subgraph.isPerfectMatching_iff_forall_degree, SimpleGraph.Subgraph.IsMatching.toEdge, SimpleGraph.Subgraph.IsMatching.even_card, SimpleGraph.Subgraph.IsPerfectMatching.even_card, SimpleGraph.Subgraph.IsMatching.sup, SimpleGraph.IsMatchingFree, SimpleGraph.exists_maximal_isMatchingFree, SimpleGraph.IsCycles, SimpleGraph.IsAlternating, SimpleGraph.Subgraph.IsPerfectMatching.symmDiff_isCycles, SimpleGraph.ConnectedComponent.odd_matches_node_outside, SimpleGraph.ConnectedComponent.even_card_of_isPerfectMatching, SimpleGraph.IsClique.even_iff_exists_isMatching, SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le, SimpleGraph.exists_bijective_of_forall_ncard_le, SimpleGraph.union_eq_univ_of_forall_ncard_le, SimpleGraph.not_isTutteViolator_of_isPerfectMatching, SimpleGraph.exists_isTutteViolator, SimpleGraph.IsTutteViolator.empty, SimpleGraph.IsTutteViolator.mono, SimpleGraph.Subgraph.IsPerfectMatching.exists_of_isClique_supp, SimpleGraph.isIndepSet_compl_iff_isVertexCover, SimpleGraph.vertexCoverNum_top, SimpleGraph.vertexCoverNum_bot, SimpleGraph.vertexCoverNum_le_card_sub_one, SimpleGraph.vertexCoverNum_exists, SimpleGraph.vertexCoverNum_lt_card, SimpleGraph.IsVertexCover.vertexCoverNum_le, SimpleGraph.universalVerts, SimpleGraph.deleteUniversalVerts, SimpleGraph.isClique_universalVerts, SimpleGraph.Subgraph.IsMatching.exists_of_universalVerts]
  E1: auto
families: []
requires: [V30.C01, V30.C02, V30.C03, V03.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Matchings and Tutte's theorem

### Overview

A matching in a graph is a set of edges no two of which share a vertex. A perfect matching covers every vertex. The questions are when a graph has a perfect matching, and how large a matching can be.

For bipartite graphs, Hall's theorem of Section 1 answers the first question, and König's theorem answers the second: the largest matching has the size of the smallest vertex cover. For general graphs the obstruction is parity. If the deletion of a set $u$ of vertices leaves more components of odd size than $u$ has vertices, no perfect matching exists. Tutte's theorem says that this is the only obstruction. Mathlib has the full proof of Tutte's theorem.

The section uses subgraphs from Chapter 1, connected components from Chapter 2, and cliques and bipartite graphs from Chapter 3.

### Definitions

**Definition (Matching).** Let $G$ be a simple graph on $V$. A *matching* of $G$ is a subgraph $M$ of $G$ in which each vertex of $M$ has exactly one neighbour in $M$. It is *perfect* if every vertex of $V$ is a vertex of $M$.

The edges of a matching are pairwise disjoint, and the vertices of $M$ are the endpoints of its edges. A perfect matching is the same as a spanning subgraph in which each vertex has degree 1.

::: mathlib
`SimpleGraph.Subgraph.IsMatching` · `Mathlib.Combinatorics.SimpleGraph.Matching`

For `M : G.Subgraph`, `M.IsMatching` is `∀ v ∈ M.verts, ∃! w, M.Adj v w`. A matching is a subgraph, not a set of edges, so its vertex set `M.verts` is part of the data. The lemma `isMatching_iff_forall_degree` gives the form `∀ v ∈ M.verts, M.degree v = 1`. The function `IsMatching.toEdge` sends each vertex of `M` to its edge.

<?decl SimpleGraph.Subgraph.IsMatching?>
:::

::: mathlib
`SimpleGraph.Subgraph.IsPerfectMatching` · `Mathlib.Combinatorics.SimpleGraph.Matching`

`M.IsPerfectMatching` is `M.IsMatching ∧ M.IsSpanning`. The lemma `isPerfectMatching_iff` gives the form `∀ v, ∃! w, M.Adj v w`, and `isPerfectMatching_iff_forall_degree` gives `∀ v, M.degree v = 1`. The predicate `G.IsMatchingFree` says that no subgraph of `G` is a perfect matching.

<?decl SimpleGraph.Subgraph.IsPerfectMatching?>
:::

**Definition (Vertex cover).** A set $c \subseteq V$ is a *vertex cover* of $G$ if each edge of $G$ has at least one endpoint in $c$. The *vertex cover number* $\tau(G)$ is the least size of a vertex cover.

A set $c$ is a vertex cover if and only if its complement is independent, that is, contains no edge.

::: mathlib
`SimpleGraph.IsVertexCover` · `Mathlib.Combinatorics.SimpleGraph.VertexCover`

`G.IsVertexCover c` is `∀ ⦃v w⦄, G.Adj v w → v ∈ c ∨ w ∈ c`. The lemma `isIndepSet_compl_iff_isVertexCover` is the link with independent sets.

<?decl SimpleGraph.IsVertexCover?>
:::

::: mathlib
`SimpleGraph.vertexCoverNum` · `Mathlib.Combinatorics.SimpleGraph.VertexCover`

`G.vertexCoverNum : ℕ∞` is the infimum of `s.encard` over the vertex covers `s`. The value lies in `ℕ∞`, so infinite graphs are allowed. The lemma `vertexCoverNum_exists` gives a cover that attains it. `vertexCoverNum_top` gives `ENat.card V - 1` for the complete graph, and `vertexCoverNum_bot` gives `0` for the empty graph.

<?decl SimpleGraph.vertexCoverNum?>
:::

**Definition (Tutte violator).** For $u \subseteq V$ let $G - u$ be the graph induced on $V \setminus u$, and let $o(G - u)$ be the number of its connected components with an odd number of vertices. The set $u$ is a *Tutte violator* if $|u| < o(G - u)$.

::: mathlib
`SimpleGraph.IsTutteViolator` · `Mathlib.Combinatorics.SimpleGraph.Tutte`

`G.IsTutteViolator u` is `u.ncard < ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents.ncard`. The graph $G - u$ is the top subgraph with the vertices of `u` deleted, coerced to a graph on its own vertex type.

<?decl SimpleGraph.IsTutteViolator?>
:::

### Theorems and proofs

**Proposition (Parity).** Let $V$ be finite. If $G$ has a perfect matching, then $|V|$ is even, and each connected component of $G$ has an even number of vertices.

*Proof.* The edges of a perfect matching partition $V$ into pairs, so $|V|$ is even. Both endpoints of a matching edge lie in the same component. So the matching edges inside a component $K$ partition $K$ into pairs, and $|K|$ is even. $\square$

**Theorem (Hall for bipartite graphs).** Let $G$ be a locally finite graph whose edges all join $p_1$ to $p_2$, for disjoint sets $p_1, p_2$. If $|s| \le |N(s)|$ for each finite $s \subseteq p_1$, then $G$ has a matching whose vertex set contains $p_1$.

*Proof.* For $x \in p_1$ let $t(x)$ be the set of neighbours of $x$. It is finite and lies in $p_2$. For a finite $s \subseteq p_1$ the union of the $t(x)$ for $x \in s$ is $N(s)$. So the family $t$ satisfies Hall's condition, and the infinite form of Hall's theorem gives an injective $f : p_1 \to p_2$ with $f(x)$ adjacent to $x$. Let $M$ be the subgraph with the edges $x f(x)$. A vertex $x \in p_1$ has the unique neighbour $f(x)$ in $M$, since $p_1$ has no inner edges. A vertex $y = f(x)$ has the unique neighbour $x$, since $f$ is injective. So $M$ is a matching, and it contains $p_1$. $\square$

::: mathlib
`SimpleGraph.exists_isMatching_of_forall_ncard_le` · `Mathlib.Combinatorics.SimpleGraph.Hall`

Under `[G.LocallyFinite]` and `G.IsBipartiteWith p₁ p₂`, the hypothesis `∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard` gives `∃ M, p₁ ⊆ M.verts ∧ M.IsMatching`. The sizes are `Set.ncard`, which is $0$ for an infinite set. The companion `exists_isPerfectMatching_of_forall_ncard_le` assumes the condition for every set `s : Set V` and gives a perfect matching.

<?decl SimpleGraph.exists_isMatching_of_forall_ncard_le?>
:::

**Proposition (Weak duality).** Let $V$ be finite, $M$ a matching with $m$ edges and $c$ a vertex cover. Then $m \le |c|$. So the largest matching has at most $\tau(G)$ edges.

*Proof.* Each edge of $M$ has an endpoint in $c$. Choose one for each edge. The edges of $M$ are disjoint, so the chosen vertices are distinct. Thus $m \le |c|$. $\square$

**Theorem (König).** Let $G$ be a finite bipartite graph with parts $p_1$ and $p_2$. The largest matching of $G$ has exactly $\tau(G)$ edges.

*Proof.* By weak duality it suffices to find a matching with $|c|$ edges for a vertex cover $c$ of least size. Put $A = c \cap p_1$ and $B = c \cap p_2$.

First, $A$ can be matched into $p_2 \setminus B$. Apply Hall's theorem to the graph of edges from $A$ to $p_2 \setminus B$. Suppose that some $S \subseteq A$ has fewer than $|S|$ neighbours in $p_2 \setminus B$. Let $T$ be this set of neighbours, and put $c' = (c \setminus S) \cup T$. Then $|c'| < |c|$. Each edge $xy$ of $G$ with $x \in S$ has $y \in B$ or $y \in T$, so it meets $c'$. Each other edge meets $c \setminus S$. So $c'$ is a vertex cover, against the choice of $c$. Thus Hall's condition holds, and there is a matching $M_1$ that covers $A$ with partners in $p_2 \setminus B$.

By the same argument there is a matching $M_2$ that covers $B$ with partners in $p_1 \setminus A$. The vertices of $M_1$ lie in $A \cup (p_2 \setminus B)$ and the vertices of $M_2$ lie in $B \cup (p_1 \setminus A)$. These sets are disjoint. So $M_1 \cup M_2$ is a matching with $|A| + |B| = |c|$ edges. $\square$

The index of this edition has no declaration for König's theorem. Mathlib has vertex covers and the bipartite Hall theorem, which are the two ingredients of the proof above.

**Theorem (Tutte).** Let $V$ be finite. The graph $G$ has a perfect matching if and only if no set $u \subseteq V$ is a Tutte violator, that is, $o(G - u) \le |u|$ for each $u$.

*Proof that the condition is necessary.* Let $M$ be a perfect matching and $u \subseteq V$. Let $K$ be an odd component of $G - u$. The matching edges with both endpoints in $K$ cover an even number of vertices of $K$. Since $|K|$ is odd, some $v \in K$ has its partner $w$ outside $K$. If $w \notin u$, then $vw$ is an edge of $G - u$, and $w$ lies in the component of $v$, which is $K$. So $w \in u$. Choose such a pair $(v_K, w_K)$ for each odd component $K$. Distinct components give distinct vertices $v_K$. The partner of a vertex in a matching is unique, so the vertices $w_K$ are also distinct. Thus $K \mapsto w_K$ is an injective map from the odd components into $u$, and $o(G - u) \le |u|$. $\square$

::: mathlib
`SimpleGraph.tutte` · `Mathlib.Combinatorics.SimpleGraph.Tutte`

For `[Finite V]`, `(∃ M : G.Subgraph, M.IsPerfectMatching) ↔ ∀ u, ¬G.IsTutteViolator u`. The easy direction is `not_isTutteViolator_of_isPerfectMatching`. Its key step is `ConnectedComponent.odd_matches_node_outside`, which gives for each odd component a vertex `v` in it and a partner `w ∈ u`. The hard direction is `exists_isTutteViolator`, which assumes that no perfect matching exists and that `Nat.card V` is even.

<?decl SimpleGraph.tutte?>
:::

*Outline of the proof that the condition is sufficient.* The proof is the one of Lovász, as in the Mathlib file. Suppose that $G$ has no perfect matching. If $|V|$ is odd, then $G - \emptyset = G$ has an odd component, so $u = \emptyset$ is a violator. Assume now that $|V|$ is even. Two facts about parity are used. First, the sizes of the components of $G - u$ add up to $|V| - |u|$, so $o(G - u) \equiv |V| - |u| \equiv |u| \pmod 2$. Second, adding edges to $G$ cannot create a violator: if $u$ is a violator for a graph $G' \ge G$ on $V$, it is one for $G$. Indeed each component of $G' - u$ is a union of components of $G - u$, and an odd one contains an odd one.

*Step 1: a maximal graph.* Among the graphs $G' \ge G$ on $V$ with no perfect matching, choose a maximal one. It suffices to find a violator for $G'$. So assume that $G$ itself is maximal: $G$ has no perfect matching, and $G + xy$ has one for each non-edge $xy$.

*Step 2: the universal vertices.* Let $U$ be the set of vertices adjacent to all other vertices. The set $U$ is a clique. The claim is that $U$ is a violator. Suppose it is not, so $o(G - U) \le |U|$.

*Step 3: the clique case.* Suppose each component of $G - U$ is a clique. For each odd component $K$ choose a distinct $w_K \in U$ and a vertex $x_K \in K$, and match $x_K$ with $w_K$. This is an edge, since $w_K$ is universal. Match the rest of $K$, which is an even clique, inside $K$. Match each even component inside itself. The unused part of $U$ has $|U| - o(G - U)$ vertices, an even number by the first parity fact, and it is a clique, so it has a perfect matching too. Together this is a perfect matching of $G$, which is impossible.

*Step 4: the other case.* Suppose some component $K$ of $G - U$ is not a clique. A connected graph that is not complete has vertices $x, y, z$ with $xy$ and $yz$ edges and $xz$ not an edge. Since $y \notin U$, there is a vertex $w$ not adjacent to $y$. By maximality, $G + xz$ has a perfect matching $M_1$ and $G + yw$ has a perfect matching $M_2$. The edge $xz$ lies in $M_1$, or else $M_1$ is a perfect matching of $G$, and $yw$ lies in $M_2$ for the same reason. In the symmetric difference of $M_1$ and $M_2$ each vertex has degree $0$ or $2$, so it is a union of disjoint cycles whose edges alternate between $M_1$ and $M_2$. A case analysis on the cycles through $xz$ and $yw$ then exchanges edges along part of a cycle, using the edges $xy$ and $yz$ of $G$. The result is a perfect matching of $G$ that avoids both $xz$ and $yw$, which is again impossible.

So $U$ is a violator. $\square$

::: mathlib
`SimpleGraph.Subgraph.IsPerfectMatching.symmDiff_isCycles` · `Mathlib.Combinatorics.SimpleGraph.Matching`

For perfect matchings `M` and `M'`, `(symmDiff M.spanningCoe M'.spanningCoe).IsCycles`. Here `G.IsCycles` says that each vertex with a neighbour has exactly two neighbours. The predicate `G.IsAlternating G'` says that of two edges of `G` at one vertex, exactly one lies in `G'`. Step 1 uses `exists_maximal_isMatchingFree`, Step 2 uses `universalVerts` and `isClique_universalVerts`, and Step 3 is `IsPerfectMatching.exists_of_isClique_supp`.

<?decl SimpleGraph.Subgraph.IsPerfectMatching.symmDiff_isCycles?>
:::

### Examples

**Example (The Petersen graph).** Take the outer cycle $0, 1, 2, 3, 4$, the inner vertices $5, \dots, 9$ with $5+i$ adjacent to $5 + ((i+2) \bmod 5)$, and the five spokes $\{i, 5+i\}$. The five spokes have pairwise disjoint endpoints and cover all ten vertices, so they form a perfect matching. Removing them leaves two disjoint 5-cycles. A 5-cycle has no perfect matching, so the complement of this matching contains no second perfect matching.

**Example (A star).** Let $G = K_{1,3}$, with centre $c$ and leaves $a_1, a_2, a_3$. The graph has 4 vertices, an even number, but no perfect matching: each edge contains $c$. The set $u = \{c\}$ is a violator, since $G - u$ has three odd components, the single leaves, and $3 > 1$. Here $\{c\}$ is a vertex cover and each matching has one edge, as König's theorem says.

**Example (An odd cycle).** The 5-cycle $C_5$ has no perfect matching since $5$ is odd. Its largest matching has 2 edges. A vertex cover needs 3 vertices: two vertices cover at most 4 edges, as each has degree 2. So $\tau(C_5) = 3$ while the largest matching has 2 edges. König's theorem fails for this graph, which is not bipartite.

**Example (Complete graphs).** The graph $K_n$ has a perfect matching if and only if $n$ is even. Its vertex cover number is $n - 1$: the complement of a cover is independent, so it has at most one vertex. Mathlib has both facts as `IsClique.even_iff_exists_isMatching` and `vertexCoverNum_top`.

### The library around it

A matching in Mathlib is a subgraph, so the lemmas about subgraphs of Chapter 1 apply. The lemma `IsMatching.sup` joins two matchings with disjoint supports.

The file `SimpleGraph.Hall` reduces to the finset form of Section 1. Its lemma `exists_bijective_of_forall_ncard_le` gives a bijection between the two parts when Hall's condition holds for every set.

The file `SimpleGraph.UniversalVerts` defines `G.universalVerts` and the subgraph `G.deleteUniversalVerts`, which Tutte's proof uses.

### Exercises

1. (A) Find all perfect matchings of the cycle $C_6$ and of the complete bipartite graph $K_{3,3}$. Hint: $C_6$ has 2 and $K_{3,3}$ has 6.
2. (A) Show that a graph on $n$ vertices with a matching of $m$ edges has $\tau(G) \ge m$, and that $\tau(G) \le 2m$ when the matching is maximal for inclusion.
3. (A) Let $G$ consist of a vertex $c$ and three disjoint triangles, with $c$ adjacent to one vertex of each triangle. Show that $G$ has 10 vertices and no perfect matching, and find a Tutte violator.
4. (B) Show that each $k$-regular bipartite graph with $k \ge 1$ has a perfect matching, using the bipartite Hall theorem. Then show that its edges split into $k$ perfect matchings.
5. (B) Deduce Hall's theorem for finite bipartite graphs from König's theorem. Hint: if no matching covers $p_1$, a cover $c$ of size less than $|p_1|$ exists. Take $s = p_1 \setminus c$.
6. (B) Prove the second parity fact of the outline: if $G \le G'$ and $u$ is a violator for $G'$, then it is one for $G$.
7. (B) Show that a tree has at most one perfect matching. Hint: a leaf must be matched with its neighbour.
8. (C) Prove Petersen's theorem. Let $G$ be cubic without bridges and $u \subseteq V$. Show that at least 3 edges join each odd component of $G - u$ to $u$, and that at most $3|u|$ edges leave $u$.
9. (C) Fill in the case analysis of Step 4 of the proof of Tutte's theorem. Hint: consider the cycle $C$ of $M_1 \triangle M_2$ that contains $yw$. If $xz$ is not on $C$, the matching $M_2 \triangle C$ works.

### Notes and history

Dénes König proved in 1931 that in a bipartite graph the largest matching has the size of the smallest vertex cover; Jenő Egerváry gave a weighted form in the same year. William Tutte proved his theorem in 1947 in "The factorization of linear graphs". The short proof through a maximal graph without a perfect matching is due to László Lovász (1975). Julius Petersen proved in 1891 that cubic graphs without bridges have perfect matchings.

The source files list these authors: `Matching` Alena Gusakov, Arthur Paulino, Kyle Miller and Pim Otte; `Tutte` and `UniversalVerts` Pim Otte; `SimpleGraph.Hall` and `VertexCover` Vlad Tsyrklevich.

### Reference

<?reference?>
