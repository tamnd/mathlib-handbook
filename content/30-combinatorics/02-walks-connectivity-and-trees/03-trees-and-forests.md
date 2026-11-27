---
title: Trees and forests
kind: theory
modules:
  - Mathlib.Combinatorics.SimpleGraph.Acyclic
explains:
  E3: [SimpleGraph.IsAcyclic, SimpleGraph.IsTree, SimpleGraph.isAcyclic_iff_subsingleton_path, SimpleGraph.IsTree.card_edgeFinset, SimpleGraph.IsTree.exists_ne_and_degree_eq_one, SimpleGraph.Connected.exists_isTree_le, SimpleGraph.isTree_iff_connected_and_card]
  E2: [SimpleGraph.IsTree.mk, SimpleGraph.IsTree.connected, SimpleGraph.IsTree.isAcyclic, SimpleGraph.isTree_iff, SimpleGraph.isAcyclic_iff_forall_not_isCycle, SimpleGraph.not_isAcyclic_iff_exists_isCycle, SimpleGraph.IsAcyclic.subsingleton_path, SimpleGraph.IsTree.existsUnique_path, SimpleGraph.isTree_iff_existsUnique_path, SimpleGraph.IsBridge, SimpleGraph.isBridge_iff, SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle, SimpleGraph.isAcyclic_iff_forall_adj_isBridge, SimpleGraph.IsTree.ncard_edgeSet_add_one, SimpleGraph.isTree_iff_isAcyclic_and_ncard_edgeSet_add_one_eq_card, SimpleGraph.IsAcyclic.ncard_edgeSet_add_card_connectedComponent, SimpleGraph.IsAcyclic.ncard_edgeSet_add_one_le_card, SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one, SimpleGraph.exists_isCycle_of_card_le, SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial, SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial, SimpleGraph.isTree_iff_minimal_connected, SimpleGraph.isTree_iff_maximal_isAcyclic, SimpleGraph.maximal_isAcyclic_iff_isTree, SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic, SimpleGraph.exists_isAcyclic_reachable_eq_le, SimpleGraph.IsAcyclic.anti, SimpleGraph.IsAcyclic.induce, SimpleGraph.isAcyclic_bot, SimpleGraph.IsAcyclic.isPath_iff_isTrail, SimpleGraph.IsAcyclic.isTree_connectedComponent, SimpleGraph.IsTree.isBipartite, SimpleGraph.IsAcyclic.isBipartite, SimpleGraph.IsTree.colorable_two, SimpleGraph.IsTree.dist_eq_dist_add_one_of_adj, SimpleGraph.IsAcyclic.cliqueFree_three, SimpleGraph.isTree_pathGraph]
  E1: auto
families: []
requires: [V30.C01, V03.C03, V03.C04, V04.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Trees and forests

### Overview

A tree is a connected graph with no cycle: removing any edge disconnects it, and adding any edge creates a cycle. A forest is a graph with no cycle, so its components are trees.

This section proves the standard characterisations. A graph is a forest if and only if any two vertices are joined by at most one path. A finite tree with at least two vertices has at least two leaves. A tree on $n$ vertices has $n - 1$ edges, and a connected graph on $n$ vertices with $n - 1$ edges is a tree. Each finite connected graph has a spanning tree. Trees are bipartite.

### Definitions

**Definition (Forest, tree, leaf).** A graph is acyclic, or a forest, when it has no cycle. A tree is a connected acyclic graph. A leaf of a graph is a vertex of degree $1$.

**Definition (Bridge).** An edge $s(u, v)$ of $G$ is a bridge when $u$ and $v$ are not joined by a walk in the graph $G \setminus \{s(u, v)\}$ obtained by deleting the edge.

**Definition (Spanning tree).** A spanning tree of $G$ is a tree $T \le G$ on the same vertex set.

::: mathlib
`SimpleGraph.IsAcyclic` · `Mathlib.Combinatorics.SimpleGraph.Acyclic`

`G.IsAcyclic` is `∀ ⦃v⦄ (c : G.Walk v v), ¬c.IsCycle`. The lemma `SimpleGraph.not_isAcyclic_iff_exists_isCycle` gives the form with an existential. Acyclicity passes to smaller graphs (`SimpleGraph.IsAcyclic.anti`) and to induced graphs (`SimpleGraph.IsAcyclic.induce`), and the empty graph is acyclic (`SimpleGraph.isAcyclic_bot`). In an acyclic graph, `SimpleGraph.IsAcyclic.isPath_iff_isTrail` says that each trail is a path.

<?decl SimpleGraph.IsAcyclic?>
:::

::: mathlib
`SimpleGraph.IsTree` · `Mathlib.Combinatorics.SimpleGraph.Acyclic`

`G.IsTree` is a structure that extends `G.Connected` with the field `isAcyclic`. So a tree has at least one vertex. `SimpleGraph.IsTree.mk` builds one from the two proofs, and `SimpleGraph.isTree_iff` states the equivalence. Each component of a forest is a tree, by `SimpleGraph.IsAcyclic.isTree_connectedComponent`. The path graphs are trees: `SimpleGraph.isTree_pathGraph`.

<?decl SimpleGraph.IsTree?>
:::

### Theorems and proofs

**Lemma (Bridges and cycles).** An edge $e = s(u, v)$ of $G$ lies on a cycle if and only if $u$ and $v$ are joined by a walk in $G \setminus \{e\}$. So $e$ is a bridge if and only if it lies on no cycle.

*Proof.* If $e$ lies on a cycle $u = v_0, v_1 = v, v_2, \ldots, v_n = u$, then the walk $v_1, \ldots, v_n$ does not use $e$, since the edges of a cycle are pairwise different.

Conversely, suppose $G \setminus \{e\}$ has a walk from $v$ to $u$. By Section 1 it has a path $q$ from $v$ to $u$. The path $q$ does not use $e$, since it lies in $G \setminus \{e\}$. Put the step from $u$ to $v$ in front of $q$. The closed walk $u, v, \ldots, u$ is a cycle: its edges are pairwise different, since $q$ is a path and $e$ is not an edge of $q$, and its vertices after the first are those of $q$, which are pairwise different. $\square$

**Theorem (Unique paths).** A graph is acyclic if and only if any two vertices are joined by at most one path. A graph is a tree if and only if any two vertices are joined by exactly one path, and there is at least one vertex.

*Proof.* Suppose $G$ has a cycle $v_0, v_1, \ldots, v_n = v_0$ with $n \ge 3$. Then the one-step path $v_1, v_0$ and the path $v_1, v_2, \ldots, v_n$ are two different paths from $v_1$ to $v_0$, of lengths $1$ and $n - 1 \ge 2$.

Conversely, suppose some pair of vertices is joined by two different paths. Among all such pairs $u, v$ and paths $p \neq q$ from $u$ to $v$, choose one with $|p| + |q|$ least. Then $u \neq v$, since the only path from $u$ to $u$ is the empty one.

Suppose $p$ and $q$ share a vertex $w \notin \{u, v\}$. Split $p$ at $w$ into a path $p_1$ from $u$ to $w$ and a path $p_2$ from $w$ to $v$, and split $q$ in the same way into $q_1$ and $q_2$. Since $p \neq q$, either $p_1 \neq q_1$ or $p_2 \neq q_2$. In the first case $|p_1| + |q_1| < |p| + |q|$, since $p_2$ is not empty, and this contradicts the minimal choice. The second case is the same. So $p$ and $q$ share only $u$ and $v$.

Now consider the closed walk $c$ that follows $p$ from $u$ to $v$ and then $q$ backwards to $u$. Its vertices after the first are the inner vertices of $p$, then $v$, then the inner vertices of $q$, then $u$. These are pairwise different. Its edges are pairwise different: an edge of $p$ and an edge of $q$ that are equal would have their two ends in both paths, so both ends would lie in $\{u, v\}$, and the edge would be $s(u, v)$. Then both $p$ and $q$ would be the one-step path from $u$ to $v$, since in a path an edge from $u$ to $v$ can only be the whole path. This contradicts $p \neq q$. So $c$ is a cycle.

The second statement follows, since connectivity gives at least one path. $\square$

::: mathlib
`SimpleGraph.isAcyclic_iff_subsingleton_path` · `Mathlib.Combinatorics.SimpleGraph.Acyclic`

`G.IsAcyclic ↔ ∀ u v, Subsingleton (G.Path u v)`: between two vertices there is at most one path. The forward direction is `SimpleGraph.IsAcyclic.subsingleton_path`. The form for trees is `SimpleGraph.isTree_iff_existsUnique_path`, `G.IsTree ↔ Nonempty V ∧ ∀ v w, ∃! p : G.Walk v w, p.IsPath`, with the direction `SimpleGraph.IsTree.existsUnique_path`. The lemma on bridges is `SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle` in `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`, with `SimpleGraph.isBridge_iff` for the definition of `SimpleGraph.IsBridge`, and `SimpleGraph.isAcyclic_iff_forall_adj_isBridge` says that a graph is acyclic if and only if each edge is a bridge.

<?decl SimpleGraph.isAcyclic_iff_subsingleton_path?>
:::

**Theorem (Leaves).** A finite tree with at least two vertices has at least two leaves.

*Proof.* The tree $T$ is connected with two vertices, so it has an edge. Paths have length less than $|V|$, so there is a path $v_0, v_1, \ldots, v_k$ of greatest length, and $k \ge 1$. Let $w$ be a neighbour of $v_0$. If $w$ is not on the path, then $w, v_0, \ldots, v_k$ is a longer path, which is impossible. If $w = v_i$ with $i \ge 2$, then $v_0, v_1, \ldots, v_i, v_0$ is a cycle, which is impossible in a tree. So $w = v_1$, and $\deg(v_0) = 1$. The same argument at the other end gives $\deg(v_k) = 1$. Since $k \ge 1$, the vertices $v_0$ and $v_k$ are different. $\square$

::: mathlib
`SimpleGraph.IsTree.exists_ne_and_degree_eq_one` · `Mathlib.Combinatorics.SimpleGraph.Acyclic`

For a tree on a nontrivial type with finitely many edges and finite degrees: `∃ u v, u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1`. The weaker `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial` gives one leaf, and `SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial` says that the minimum degree is $1$.

<?decl SimpleGraph.IsTree.exists_ne_and_degree_eq_one?>
:::

**Lemma (Removing a leaf).** Let $T$ be a tree with at least two vertices and $\ell$ a leaf. Then $T - \ell$, the graph induced on the other vertices, is a tree.

*Proof.* It is acyclic, since a cycle of $T - \ell$ is a cycle of $T$. It is connected: let $a, b \neq \ell$, and let $p$ be the path in $T$ from $a$ to $b$. An inner vertex of a path has two different neighbours on the path, so it has degree at least $2$, and $\ell$ is not an inner vertex. So $p$ lies in $T - \ell$. $\square$

**Theorem (Edges of a tree).** A tree on $n$ vertices has $n - 1$ edges.

*Proof.* Induction on $n$. A tree on one vertex has no edge. Let $n \ge 2$ and let $T$ be a tree on $n$ vertices. By the theorem on leaves it has a leaf $\ell$. By the lemma, $T - \ell$ is a tree on $n - 1$ vertices, so it has $n - 2$ edges by the induction hypothesis. The edges of $T$ are those of $T - \ell$ and the one edge at $\ell$. So $T$ has $n - 1$ edges. $\square$

::: mathlib
`SimpleGraph.IsTree.card_edgeFinset` · `Mathlib.Combinatorics.SimpleGraph.Acyclic`

`G.IsTree → #G.edgeFinset + 1 = Fintype.card V`. The form with `Set.ncard` and `Nat.card` is `SimpleGraph.IsTree.ncard_edgeSet_add_one`. The `+ 1` avoids the truncated subtraction of `ℕ`. The library proof maps each vertex other than a fixed root to the first edge of its path to the root, a bijection onto the edges.

<?decl SimpleGraph.IsTree.card_edgeFinset?>
:::

**Corollary (Forests).** A forest on $n$ vertices with $c$ components has $n - c$ edges.

*Proof.* Each component is a tree, since it is connected and its cycles would be cycles of the forest. A component with $n_i$ vertices has $n_i - 1$ edges, each edge lies in one component, and $\sum_i (n_i - 1) = n - c$. $\square$

**Theorem (Spanning trees).** Each finite connected graph $G$ has a spanning tree. So a connected graph on $n$ vertices has at least $n - 1$ edges.

*Proof.* Among the connected spanning subgraphs $H \le G$, of which $G$ is one, choose one with the least number of edges. Suppose $H$ has a cycle, and let $e$ be an edge on it. By the lemma on bridges, the ends of $e$ are joined by a walk in $H \setminus \{e\}$. So each walk in $H$ can avoid $e$: replace each use of $e$ by that walk. Hence $H \setminus \{e\}$ is connected, and it has fewer edges than $H$. This contradicts the choice. So $H$ is acyclic, and it is a spanning tree. It has $n - 1$ edges, all of them edges of $G$. $\square$

::: mathlib
`SimpleGraph.Connected.exists_isTree_le` · `Mathlib.Combinatorics.SimpleGraph.Acyclic`

`G.Connected → ∃ T ≤ G, T.IsTree`, with no finiteness hypothesis. On an infinite graph the minimal choice of the proof above fails, and the library uses a maximal acyclic subgraph instead, which exists by Zorn's lemma (Volume 4, Chapter 1). The general form `SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic` extends a given acyclic subgraph, and `SimpleGraph.exists_isAcyclic_reachable_eq_le` gives a spanning forest of any graph. The bound on the edges is `SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`.

<?decl SimpleGraph.Connected.exists_isTree_le?>
:::

**Theorem (Characterisations of finite trees).** For a graph $G$ on $n \ge 1$ vertices, the following are equivalent: (a) $G$ is a tree; (b) $G$ is connected and has $n - 1$ edges; (c) $G$ is acyclic and has $n - 1$ edges.

*Proof.* (a) implies (b) and (c) by the theorem on edges. (b) implies (a): let $T \le G$ be a spanning tree. It has $n - 1$ edges, as many as $G$, so $T = G$. (c) implies (a): by the corollary on forests, $G$ has $n - c$ edges, where $c$ is the number of components. So $c = 1$, and $G$ is connected. $\square$

The same counts give: a graph on $n$ vertices with at least $n$ edges has a cycle, since a forest has at most $n - 1$ edges.

::: mathlib
`SimpleGraph.isTree_iff_connected_and_card` · `Mathlib.Combinatorics.SimpleGraph.Acyclic`

`G.IsTree ↔ G.Connected ∧ Nat.card G.edgeSet + 1 = Nat.card V` on a finite type. The form (c) is `SimpleGraph.isTree_iff_isAcyclic_and_ncard_edgeSet_add_one_eq_card`. The forest count is `SimpleGraph.IsAcyclic.ncard_edgeSet_add_card_connectedComponent`, the bound for forests is `SimpleGraph.IsAcyclic.ncard_edgeSet_add_one_le_card`, and `SimpleGraph.exists_isCycle_of_card_le` gives a cycle from $n$ edges. The order forms are `SimpleGraph.isTree_iff_minimal_connected`, `SimpleGraph.isTree_iff_maximal_isAcyclic` and `SimpleGraph.maximal_isAcyclic_iff_isTree`.

<?decl SimpleGraph.isTree_iff_connected_and_card?>
:::

**Proposition (Trees are bipartite).** The vertices of a tree can be coloured with two colours so that adjacent vertices have different colours.

*Proof.* Induction on the number of vertices. A tree on one vertex gets one colour. For $n \ge 2$, remove a leaf $\ell$ with neighbour $m$. Colour the tree $T - \ell$ by the induction hypothesis, and give $\ell$ the colour that $m$ does not have. The only edge at $\ell$ goes to $m$, so the colouring is proper. $\square$

The library colours $v$ by the parity of $d(r, v)$ for a root $r$, using `SimpleGraph.IsTree.dist_eq_dist_add_one_of_adj`. The results are `SimpleGraph.IsTree.isBipartite`, `SimpleGraph.IsAcyclic.isBipartite` and `SimpleGraph.IsTree.colorable_two`; Chapter 3 defines colourings. A forest has no triangle: `SimpleGraph.IsAcyclic.cliqueFree_three`.

### Examples

**Example (The trees on four vertices).** A tree on $\{1, 2, 3, 4\}$ has $3$ edges. Its degrees sum to $6$, and each degree is at least $1$, so the degree sequence is $3, 1, 1, 1$ (a star) or $2, 2, 1, 1$ (a path). A star is determined by its center: $4$ trees. A path is a sequence of the four vertices up to reversal: $4!/2 = 12$ trees. So there are $16 = 4^{2}$ labelled trees on four vertices, in agreement with the formula $n^{n-2}$ of Cayley. The index of this edition has no declaration for the formula of Cayley.

**Example (A spanning tree of the Petersen graph).** Start at $\{1,2\}$. Take the three edges to its neighbours $\{3,4\}, \{3,5\}, \{4,5\}$. Each neighbour has two further neighbours: $\{3,4\}$ has $\{1,5\}$ and $\{2,5\}$, $\{3,5\}$ has $\{1,4\}$ and $\{2,4\}$, and $\{4,5\}$ has $\{1,3\}$ and $\{2,3\}$. These six vertices are pairwise different and different from the first four, so the six edges to them give $3 + 6 = 9$ edges on all $10$ vertices. The result is connected with $9 = 10 - 1$ edges, so it is a spanning tree by the characterisation. The Petersen graph has $15$ edges, so $15 - 9 = 6$ edges lie outside the tree. By Exercise 8 they close six different cycles with the tree.

**Counterexample (Connected with $n - 1$ edges needs both).** The graph on $\{1, 2, 3, 4\}$ with the edges $12, 23, 31$ has $3 = n - 1$ edges, but it has a cycle and the vertex $4$ is isolated. It satisfies neither (b) nor (c), and the count of edges alone does not decide.

### The library around it

The file `Mathlib.Combinatorics.SimpleGraph.Acyclic` has the definitions, the theorem on unique paths, the counts of edges, the leaves, spanning trees and forests, and the colourings of forests. The bridges are in `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`, where `SimpleGraph.Preconnected.connected_deleteEdges_of_not_isBridge` is the step of the proof of the spanning tree theorem. Newer statements count with `Set.ncard` and `Nat.card`, older ones with `Finset.card` and `Fintype.card`.

Common errors of a learner:

- `G.IsTree` includes `Nonempty V`. The empty graph on the empty type is acyclic but not a tree.
- The count of edges is stated as `#G.edgeFinset + 1 = Fintype.card V`, not with a subtraction. Rewrite the goal in this form first.
- `G.IsAcyclic` speaks of cycles of `G`, which have length at least $3$. A walk $u, v, u$ is not a cycle, so a single edge is acyclic.

### Exercises

1. (A) Show that the path on $n$ vertices and the star $K_{1, n-1}$ are trees, and count their leaves.
2. (A) Show that each edge of a tree is a bridge and that adding an edge to a tree creates exactly one cycle.
3. (A) Show that a tree with a vertex of degree $k$ has at least $k$ leaves.
4. (A) A forest has $20$ vertices and $15$ edges. How many components does it have?
5. (B) Let $T$ be a tree on $n \ge 2$ vertices with $n_i$ vertices of degree $i$. Show that $n_1 = 2 + \sum_{i \ge 3} (i - 2) n_i$. Hint: compute the degree sum in two ways.
6. (B) Show that a finite graph with $|E| \ge |V|$ has a cycle, without the spanning tree theorem. Hint: remove leaves and isolated vertices.
7. (B) Draw all the trees on five vertices up to isomorphism, and count the labelled ones. Check the answer against $5^{3} = 125$.
8. (B) Let $T$ be a spanning tree of a connected graph $G$ and $e$ an edge of $G$ not in $T$. Show that $T$ plus $e$ has exactly one cycle, and that the cycles of different edges $e$ are different.
9. (C) Show that the center of a finite tree is a single vertex or two adjacent vertices. Hint: remove all leaves and show that the center does not change.
10. (C) Let $T_1$ and $T_2$ be spanning trees of $G$ and $e$ an edge of $T_1$ not in $T_2$. Show that there is an edge $f$ of $T_2$ not in $T_1$ such that $T_1$ with $e$ replaced by $f$ is a spanning tree.

### Notes and history

Cayley used trees in 1857 to count the isomers of chemical compounds, and stated the formula $n^{n-2}$ for labelled trees in 1889. Prüfer gave a bijective proof by codes in 1918. Kirchhoff counted spanning trees with determinants in 1847 in his work on electrical networks. The exchange property of Exercise 10 is the first example of a matroid, the subject of Whitney in 1935. The header of `Mathlib.Combinatorics.SimpleGraph.Acyclic` lists Kyle Miller and Snir Broshi.

### Reference

<?reference?>
