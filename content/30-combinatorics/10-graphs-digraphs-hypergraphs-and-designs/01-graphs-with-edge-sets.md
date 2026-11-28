---
title: Graphs with edge sets
kind: api
modules:
  - Mathlib.Combinatorics.Graph.Basic
  - Mathlib.Combinatorics.Graph.Connected.EdgeCut
  - Mathlib.Combinatorics.Graph.Delete
  - Mathlib.Combinatorics.Graph.Lattice
  - Mathlib.Combinatorics.Graph.Maps
  - Mathlib.Combinatorics.Graph.Simple
  - Mathlib.Combinatorics.Graph.Subgraph
explains:
  E2: [Graph.le_iff_compatible_subset_subset, Graph.Compatible.edgeSet_inf, Graph.deleteEdges_deleteEdges, Graph.edgeCut_eq_empty_iff, Graph.edgeCut_symmDiff, Graph.isBond_singleton_iff_isBridge, Graph.IsBond.isBridge_deleteEdges]
  E1: auto
families: []
requires: [V30.C01, V30.C02, V03.C03, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Graphs with edge sets

### Overview

A `SimpleGraph V` of Chapter 1 is a symmetric irreflexive relation on $V$. It has no loops, no parallel edges and no names for its edges. Many arguments need more than this. A contraction makes loops and parallel edges, a cut is a set of edges, and the edges of a multigraph must have their own identity. The type `Graph α β` gives this structure. A graph has a set of vertices in `α`, a set of edges in `β`, and an incidence relation that gives the two ends of each edge.

The design follows `Matroid` of Chapter 9. A graph is not a structure on a whole type. It is a pair of sets inside the types `α` and `β`, together with a relation. So a subgraph of `G : Graph α β` is again a term of `Graph α β`, and the subgraph order is a partial order on one type. The cost is that a lemma must often say that a vertex is in $V(G)$ or an edge is in $E(G)$.

This section describes the basic type, the kinds of subgraphs, the deletion operations, the intersection, the images under maps of vertices, the comparison with simple graphs, and the edge cuts, bridges and bonds.

### The library around it

#### The type and its incidence relation

The structure `Graph` has the fields `Graph.vertexSet` with the notation `V(G)`, `Graph.edgeSet` with the notation `E(G)`, and the relation `Graph.IsLink`. The statement `G.IsLink e x y` says that $e$ is an edge of $G$ with the ends $x$ and $y$. The axioms say that the relation is symmetric, that an edge has at most two ends, that an edge is in $E(G)$ if and only if it links some pair, and that the ends of an edge are vertices.

| Lean name | Statement |
|---|---|
| `Graph.IsLink.symm` | if $e$ links $x$ to $y$, then $e$ links $y$ to $x$ |
| `Graph.isLink_comm` | the same as an `Iff` |
| `Graph.IsLink.left_mem` | an end of an edge is in $V(G)$ |
| `Graph.IsLink.edge_mem` | an edge that links two vertices is in $E(G)$ |
| `Graph.IsLink.right_unique` | if $e$ links $x$ to $y$ and $x$ to $z$, then $y = z$ |
| `Graph.ext` | two graphs with the same vertex sets and the same links are equal |

Three relations come from `IsLink`. `G.Inc e x` says that $x$ is an end of $e$. `G.IsLoopAt e x` says that both ends of $e$ are $x$, and `G.IsNonloopAt e x` says that $e$ has the end $x$ and an end other than $x$. `G.Adj x y` says that some edge links $x$ to $y$. If `h : G.Inc e x`, then `h.other` is the other end of $e$, and `Graph.Inc.isLink_other` says that $e$ links $x$ to `h.other`. For a loop the other end is $x$ again. `Graph.Inc.isLoopAt_or_isNonloopAt` splits each incidence into the two cases.

A loop at $x$ is a link from $x$ to $x$, and two edges $e \neq f$ can link the same pair. So `Graph α β` covers multigraphs with loops. The sets `G.incidenceSet x` and `G.loopSet x` collect the edges at $x$ and the loops at $x$. Three small examples are in the library. `Graph.noEdge V β` has the vertex set $V$ and no edges. `Graph.banana u v E` has the vertices $u$ and $v$ and the edge set $E$, where each edge links $u$ to $v$. `Graph.bouquet v E` has the single vertex $v$ and the edge set $E$, where each edge is a loop at $v$. By `Graph.banana_adj`, two vertices are adjacent in `banana u v E` if and only if $E$ is nonempty and $\{x, y\} = \{u, v\}$.

Two graphs are compatible if they agree on each common edge: `G.Compatible H` says that for each $e \in E(G) \cap E(H)$, $e$ links the same pairs in $G$ and in $H$. Graphs with disjoint edge sets are compatible (`Graph.Compatible.of_disjoint_edgeSet`).

#### Four kinds of subgraphs

The order `H ≤ G` is `Graph.IsSubgraph`. It says that $V(H) \subseteq V(G)$ and that each link of $H$ is a link of $G$. It is the simp normal form, and `Graph.isSubgraph_iff_le` converts between the two forms.

**Theorem.** $H \le G$ if and only if $H$ and $G$ are compatible, $V(H) \subseteq V(G)$ and $E(H) \subseteq E(G)$.

*Proof.* Let $H \le G$. Each edge of $H$ links some pair in $H$, so it links the same pair in $G$, and $E(H) \subseteq E(G)$. Let $e \in E(H)$ link $x$ to $y$ in $G$. The edge $e$ links some $u$ to $v$ in $H$, so in $G$ it links $u$ to $v$ and $x$ to $y$. An edge of $G$ has at most two ends, so $\{x, y\} = \{u, v\}$ and $e$ links $x$ to $y$ in $H$. So the graphs are compatible. Conversely, let $e$ link $x$ to $y$ in $H$. Then $e \in E(H) \subseteq E(G)$, and compatibility gives that $e$ links $x$ to $y$ in $G$. $\square$

This is `Graph.le_iff_compatible_subset_subset`. So two subgraphs of one graph are compatible (`Graph.Compatible.of_le_le`), and inside a fixed $G$ a subgraph is fixed by its vertex set and its edge set.

Three stronger relations have their own notation. Each one extends `H ≤ G`.

| Notation | Lean name | Extra condition |
|---|---|---|
| `H ≤s G` | `Graph.IsSpanningSubgraph` | $V(H) = V(G)$ |
| `H ≤i G` | `Graph.IsInducedSubgraph` | each link of $G$ between two vertices of $H$ is a link of $H$ |
| `H ≤c G` | `Graph.IsClosedSubgraph` | $H$ is induced, and each edge of $G$ at a vertex of $H$ is in $E(H)$ |

A closed subgraph is a union of components of $G$. The notations `≤i` and `≤c` are scoped in the namespace `Graph`. The bottom graph `⊥` has no vertices and no edges, and `Graph.ne_bot_iff` says that $G \neq \bot$ if and only if $V(G)$ is nonempty.

#### Deletion and induced subgraphs

The module `Mathlib.Combinatorics.Graph.Delete` gives four operations.

| Lean name | Vertex set | Edge set |
|---|---|---|
| `Graph.restrict G F` | $V(G)$ | $E(G) \cap F$ |
| `Graph.deleteEdges G F` | $V(G)$ | $E(G) \setminus F$ |
| `Graph.induce G X` | $X$ | the edges of $G$ with both ends in $X$ |
| `Graph.deleteVerts G X` | $V(G) \setminus X$ | the edges of $G$ with no end in $X$ |

The two edge operations are related: `Graph.restrict_eq_deleteEdges` says that `G.restrict F = G.deleteEdges (E(G) \ F)`. The vertex operations are related in the same way, because `G.deleteVerts X` is `G.induce (V(G) \ X)`. The edge set of `G.induce X` is `Graph.edgeSet_induce`. The set $X$ in `induce` can contain points outside $V(G)$, and then `G.induce X` is not a subgraph of $G$. The lemma `Graph.induce_le_iff` says that `G.induce X ≤ G` if and only if $X \subseteq V(G)$.

**Theorem.** $(G \setminus F_1) \setminus F_2 = G \setminus (F_1 \cup F_2)$.

*Proof.* Both sides have the vertex set $V(G)$. An edge $e$ links $x$ to $y$ on the left if and only if $e$ links $x$ to $y$ in $G$, $e \notin F_1$ and $e \notin F_2$. This is the condition on the right. $\square$

This is `Graph.deleteEdges_deleteEdges`. The intersection form for `restrict` is `Graph.restrict_restrict`.

#### Intersection

The module `Mathlib.Combinatorics.Graph.Lattice` makes `Graph α β` a `SemilatticeInf`. The vertex set of $G \sqcap H$ is $V(G) \cap V(H)$, and $e$ links $x$ to $y$ in $G \sqcap H$ if and only if it does so in both graphs (`Graph.inf_isLink`). An edge in $E(G) \cap E(H)$ with different ends in $G$ and in $H$ is not an edge of $G \sqcap H$. So the edge set of the intersection is in general smaller than $E(G) \cap E(H)$ (`Graph.edgeSet_inf`).

**Theorem.** If $G$ and $H$ are compatible, then $E(G \sqcap H) = E(G) \cap E(H)$.

*Proof.* By `Graph.edgeSet_inf`, an edge of $G \sqcap H$ is an edge $e \in E(G) \cap E(H)$ that links the same pairs in $G$ and $H$. Compatibility gives the second condition for each such $e$. $\square$

This is `Graph.Compatible.edgeSet_inf`. Two graphs are disjoint in this order if and only if their vertex sets are disjoint (`Graph.disjoint_iff`). The module gives no join. Two incompatible graphs have no common upper bound, because an edge with different ends in $G$ and $H$ cannot have both pairs of ends in one graph.

#### Maps of vertices

For $f : \alpha \to \alpha'$, the graph `Graph.map f G` has the vertex set $f(V(G))$ and the same edge set as $G$. An edge that links $x$ to $y$ in $G$ links $f(x)$ to $f(y)$ in the image (`Graph.IsLink.map`). If $f(x) = f(y)$ for an edge of $G$ with the ends $x \neq y$, then the edge becomes a loop. So `map` is the operation that identifies vertices. The adjacency of the image is `Graph.map_adj`, stated with `Relation.Map`. The functor laws are `Graph.map_id` and `Graph.map_map`, and `Graph.map_eq_of_eqOn` says that the image depends only on $f$ on $V(G)$.

#### Comparison with simple graphs

The class `Graph.Loopless` says that $G$ has no loops, and `Graph.Simple` extends it with the condition that two edges with the same ends are equal (`Graph.IsLink.eq`). Both classes pass to subgraphs (`Graph.Loopless.anti`, `Graph.Simple.anti`).

The function `Graph.toSimpleGraph` sends `G : Graph α β` to a `SimpleGraph` on the subtype `V(G)`. Two vertices are adjacent if they are distinct and adjacent in $G$. It forgets the loops and the names of the edges. For a loopless graph, `Graph.toSimpleGraph_adj_iff` removes the condition $u \neq v$. In the other direction, `Graph.ofSimpleGraph G` sends a simple graph on `α` to a graph in `Graph α (Sym2 α)`, with the vertex set `univ` and the edges `s(x, y)` of `G.edgeSet`. Its adjacency is that of $G$ (`Graph.ofSimpleGraph_adj_iff`). The round trip from a simple graph is the isomorphism `Graph.toSimpleGraphOfSimpleGraphIso`. The round trip from a simple `Graph` is not yet in the library.

#### Edge cuts, bridges and bonds

For a set $S$ of vertices, `Graph.edgeCut G S` is the set of edges with one end in $S$ and one end outside $S$. A loop is never in a cut. The cut does not change if $S$ is replaced by $V(G) \setminus S$ (`Graph.edgeCut_vertexSet_diff`).

**Theorem.** Let $S \subseteq V(G)$. Then $\delta(S) = \emptyset$ if and only if `G.induce S ≤c G`.

*Proof.* The graph `G.induce S` is induced, and it is a subgraph because $S \subseteq V(G)$. So the closed condition is the only open point. Let $\delta(S) = \emptyset$, let $e$ be an edge of $G$ at $x \in S$, and let $y$ be its other end. If $y \notin S$, then $e \in \delta(S)$. So $y \in S$, and $e$ is an edge of `G.induce S`. Conversely, let the induced graph be closed and let $e$ link $u \in S$ to $v$. Then $e$ is an edge of `G.induce S`, so $v \in S$ and $e \notin \delta(S)$. $\square$

This is `Graph.edgeCut_eq_empty_iff`. The cuts form a vector space over $\mathbb{F}_2$, which is the cut space of the graph. The next statement is the main step.

**Theorem.** $\delta(S \mathbin{\triangle} S') = \delta(S) \mathbin{\triangle} \delta(S')$.

*Proof.* Let $e$ link $u$ to $v$ and let $[P]$ be $1$ if $P$ holds and $0$ if not. Then $e \in \delta(S)$ if and only if $[u \in S] + [v \in S] = 1$ in $\mathbb{F}_2$. Also $[u \in S \mathbin{\triangle} S'] = [u \in S] + [u \in S']$. So $e \in \delta(S \mathbin{\triangle} S')$ if and only if $[u \in S] + [v \in S] + [u \in S'] + [v \in S'] = 1$, which says that $e$ is in exactly one of $\delta(S)$ and $\delta(S')$. $\square$

This is `Graph.edgeCut_symmDiff`. A set $F$ of edges is an edge cut (`Graph.IsEdgeCut`) if it is $\delta(S)$ for some $S$. So `Graph.IsEdgeCut.symmDiff` says that the edge cuts are closed under symmetric difference.

An edge $e$ is a bridge (`Graph.IsBridge`) if $\{e\}$ is an edge cut. A bond (`Graph.IsBond`) is a minimal nonempty edge cut. It uses `Minimal` from Volume 4, Chapter 1.

**Theorem.** $\{e\}$ is a bond if and only if $e$ is a bridge.

*Proof.* A bond is an edge cut, so one direction is clear. Conversely, let $\{e\}$ be an edge cut. It is nonempty, and its only proper subset is $\emptyset$, which is not nonempty. So $\{e\}$ is minimal. $\square$

This is `Graph.isBond_singleton_iff_isBridge`. A deeper statement is `Graph.IsBond.isBridge_deleteEdges`: if $B$ is a bond and $e \in B$, then $e$ is a bridge of the graph `G.deleteEdges (B \ {e})`. So the deletion of all other edges of a bond leaves the last edge as a bridge. Cuts and bridges are local to components: an edge cut of a closed subgraph is an edge cut of the whole graph (`Graph.IsEdgeCut.of_isClosedSubgraph`), and `Graph.IsClosedSubgraph.isBridge_iff` compares the bridges.

#### Common errors

1. A learner writes `G.induce X` and expects a subgraph of $G$ for each $X$. The vertex set of `G.induce X` is $X$ itself, so a point of $X$ outside $V(G)$ is an isolated vertex of `G.induce X`. Use `Graph.induce_le_iff` with the hypothesis $X \subseteq V(G)$.
2. A learner expects $E(G \sqcap H) = E(G) \cap E(H)$ in general. This needs `G.Compatible H`. Without it, a common edge with different ends in $G$ and $H$ is dropped.
3. A learner expects `Graph.toSimpleGraph G` to be a graph on `α`. It is a graph on the subtype `V(G)`, so its vertices are pairs of a point and a proof of membership.

### Exercises

1. (A) Describe `Graph.bouquet v E` with three loops, and compute `incidenceSet v` and `loopSet v`. Is it `Loopless`?
2. (A) Show that `Graph.banana u v E` with $u \ne v$ and $|E| \ge 2$ is loopless but not `Simple`.
3. (A) Let $G$ be a cycle with the vertices $1, 2, 3, 4$ and the edges $a = 12$, $b = 23$, $c = 34$, $d = 41$. Compute $\delta(\{1\})$, $\delta(\{1, 2\})$ and their symmetric difference, and check `Graph.edgeCut_symmDiff`.
4. (B) In the graph of Exercise 3, show that $\{a, c\}$ is a bond and that $G$ has no bridge. Then check `Graph.IsBond.isBridge_deleteEdges` for $B = \{a, c\}$ and $e = a$.
5. (B) Let $G$ be a graph with one edge $e$ that links $1$ to $2$, and let $f$ map both $1$ and $2$ to $0$. Describe `Graph.map f G`, and show that $e$ is a loop of the image.
6. (C) Show that $F$ is an edge cut of $G$ if and only if each cycle of $G$ meets $F$ in an even number of edges. Which direction follows from the definition of `Graph.edgeCut` alone?

### Reference

<?reference?>
