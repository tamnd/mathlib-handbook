---
title: Connected subgraphs, edge connectivity and ends
kind: api
modules:
  - Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
  - Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
  - Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
  - Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
  - Mathlib.Combinatorics.SimpleGraph.Ends.Defs
  - Mathlib.Combinatorics.SimpleGraph.Ends.Properties
explains:
  E2: [SimpleGraph.induce_union_connected, SimpleGraph.Walk.isInduced_toSubgraph, SimpleGraph.odd_ncard_oddComponents, SimpleGraph.ConnectedComponent.Represents.ncard_eq, SimpleGraph.IsEdgeConnected.le_degree, SimpleGraph.isEdgeConnected_two_iff_forall_not_isBridge, SimpleGraph.nonempty_ends_of_infinite]
  E1: auto
families: []
requires: [V30.C01, V03.C03, V03.C05, V24.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Connected subgraphs, edge connectivity and ends

### Overview

Section 2 of this chapter defines connectivity for a whole graph: reachability, connected graphs and connected components. Proofs in graph theory also need connectivity for parts of a graph. A walk spans a connected subgraph, an induced subgraph on a set of vertices can be connected or not, and a component is a maximal connected subgraph. The first module of this section holds these facts. Two further modules give decidability and counting for components of finite graphs, and the notion of a set of representatives of components, which the proof of Tutte's theorem in Chapter 4 uses.

The section then measures how well a graph is connected. A graph is $k$-edge-connected when it stays connected after the deletion of any $k - 1$ edges. The library states this for each pair of vertices and for the graph, with $k$ in `ℕ∞`. The last two modules study infinite graphs. Remove a finite set $K$ of vertices from a connected, locally finite, infinite graph: finitely many components remain, and some of them are infinite. An end is a coherent choice of an infinite component for every $K$. The ends describe the ways to go to infinity in the graph. The two-way infinite path has two ends, and the infinite grid has one.

### The library around it

#### Connected subgraphs

The module `Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph` defines connectivity for a subgraph `H : G.Subgraph` of Chapter 1. The predicates `SimpleGraph.Subgraph.Preconnected` and `SimpleGraph.Subgraph.Connected` are structures with one field: the graph `H.coe` on the subtype of vertices of `H` is preconnected or connected. The structure exists so that dot notation finds the lemmas of `Subgraph` and not those of `SimpleGraph`. The unfolded forms are `SimpleGraph.Subgraph.preconnected_iff` and `SimpleGraph.Subgraph.connected_iff'`, and `SimpleGraph.Subgraph.connected_iff` states that a connected subgraph is a preconnected subgraph with a nonempty vertex set.

A walk spans a subgraph. For `p : G.Walk u v`, the subgraph `p.toSubgraph` has the vertices of `p` (`SimpleGraph.Walk.verts_toSubgraph`) and the edges of `p` (`SimpleGraph.Walk.edgeSet_toSubgraph`). Its adjacency is described by positions in `SimpleGraph.Walk.toSubgraph_adj_iff`: $u' \sim v'$ in `p.toSubgraph` when $s(u', v') = s(v_i, v_{i+1})$ for some $i$ less than the length. The subgraph of a walk is connected (`SimpleGraph.Walk.toSubgraph_connected`). It is the same for a walk and its reverse (`SimpleGraph.Walk.toSubgraph_reverse`), and the subgraph of an append is the supremum of the subgraphs (`SimpleGraph.Walk.toSubgraph_append`). The walk also lives in its own subgraph: `p.mapToSubgraph` is `p` as a walk of `p.toSubgraph.coe`. This form keeps paths, trails, cycles and circuits (`SimpleGraph.Walk.isPath_mapToSubgraph`, `SimpleGraph.Walk.isCycle_mapToSubgraph` and the others). For a cycle each vertex has exactly two neighbours in the subgraph (`SimpleGraph.Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two`).

**Theorem.** The subgraph spanned by a walk `p` is induced if and only if `p` is chordless.

*Proof.* The subgraph has the vertices of `p` and the edges of `p`. It is induced when it contains each edge of $G$ between two of its vertices, that is each edge of $G$ between two vertices of `p`. By `SimpleGraph.Walk.isChordless_iff_forall_mem_edges` of Section 4, this is the definition of a chordless walk. $\square$

This is `SimpleGraph.Walk.isInduced_toSubgraph`. The module also treats the induced graphs `G.induce s` on a set $s$ of vertices. The forms `SimpleGraph.connected_induce_iff` and `SimpleGraph.preconnected_induce_iff` compare `G.induce s` with the induced subgraph `(⊤ : G.Subgraph).induce s`.

**Theorem.** Let $s$ and $t$ be sets of vertices such that $G[s]$ and $G[t]$ are preconnected and $s \cap t$ is nonempty. Then $G[s \cup t]$ is connected.

*Proof.* Fix $w \in s \cap t$. A vertex $x \in s$ reaches $w$ inside $G[s]$, and the walk lies in $G[s \cup t]$. The same holds for $x \in t$ with $G[t]$. So each vertex of $s \cup t$ reaches $w$ in $G[s \cup t]$, and the vertex set is nonempty. $\square$

This is `SimpleGraph.induce_union_connected`. Its relatives are `SimpleGraph.induce_pair_connected_of_adj` (two adjacent vertices induce a connected graph), `SimpleGraph.induce_sUnion_connected_of_pairwise_not_disjoint` for a family of sets, and `SimpleGraph.induce_connected_of_patches`, which builds a connected induced graph from connected pieces that all contain one vertex. In a preconnected graph each nonempty finset of vertices lies in a finset that induces a connected graph (`SimpleGraph.extend_finset_to_connected`). A connected component gives a subgraph `C.toSubgraph`, and it is a maximal connected subgraph (`SimpleGraph.ConnectedComponent.maximal_connected_toSubgraph`). Conversely a maximal connected subgraph is the subgraph of a component (`SimpleGraph.ConnectedComponent.maximal_subgraph_connected_iff`).

#### Components of finite graphs

The module `Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite` makes connectivity decidable on a finite type with decidable adjacency. The instances `SimpleGraph.instDecidableRelReachable`, `SimpleGraph.instDecidablePreconnected` and `SimpleGraph.instDecidableConnected` decide reachability by a search over walks of length less than the number of vertices (`SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty`). The instance `SimpleGraph.instFintypeConnectedComponent` makes the type of components finite, so `Fintype.card G.ConnectedComponent` counts them. Fewer edges give more components (`SimpleGraph.ConnectedComponent.card_le_card_of_le`).

The set of odd components `G.oddComponents` holds the components with an odd number of vertices. Tutte's theorem in Chapter 4 counts them.

**Theorem.** On a finite type $V$, the number of odd components of $G$ is odd if and only if $|V|$ is odd.

*Proof.* The components partition $V$, so $|V|$ is the sum of the sizes of the components. Modulo $2$ the even components contribute $0$ and each odd component contributes $1$. So $|V|$ is congruent to the number of odd components modulo $2$. $\square$

This is `SimpleGraph.odd_ncard_oddComponents`. Adding edges merges components and cannot create odd components: `SimpleGraph.ncard_oddComponents_mono` states that $G \le G'$ implies that $G'$ has at most as many odd components as $G$. The proof uses `SimpleGraph.ConnectedComponent.odd_oddComponents_ncard_subset_supp`: an odd component of $G'$ contains an odd number of odd components of $G$, hence at least one.

#### Sets of representatives

The module `Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents` defines `SimpleGraph.ConnectedComponent.Represents s C` for a set $s$ of vertices and a set $C$ of components. The definition is `Set.BijOn G.connectedComponentMk s C`: the map that sends a vertex to its component is a bijection from $s$ onto $C$. So $s$ holds exactly one vertex of each component of $C$ and no other vertex (`SimpleGraph.ConnectedComponent.Represents.existsUnique_rep`). With choice, each set of components has a set of representatives (`SimpleGraph.ConnectedComponent.Represents.image_out`).

**Theorem.** If $s$ represents $C$, then $s$ and $C$ have the same number of elements.

*Proof.* A bijection between two sets keeps the number of elements, and the definition gives a bijection from $s$ onto $C$. $\square$

This is `SimpleGraph.ConnectedComponent.Represents.ncard_eq`, with `ncard` for possibly infinite sets. The lemmas `SimpleGraph.ConnectedComponent.Represents.ncard_inter` and `SimpleGraph.ConnectedComponent.Represents.ncard_sdiff_of_mem` count the representatives inside one component. The form for odd components is `SimpleGraph.ConnectedComponent.even_ncard_supp_sdiff_rep`: if $s$ represents the odd components, then each component without its representative has an even number of vertices. The proof of Tutte's theorem removes one vertex from each odd component in this way.

#### Edge connectivity

The module `Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity` defines `G.IsEdgeReachable k u v` for `k : ℕ∞`. It holds when $u$ and $v$ stay reachable after the deletion of any set of fewer than $k$ edges. The graph is $k$-edge-connected, `G.IsEdgeConnected k`, when every pair of vertices is $k$-edge-reachable. The form `SimpleGraph.isEdgeConnected_iff` states the graph version directly: the deletion of fewer than $k$ edges leaves a preconnected graph.

The small values of $k$ are the notions of Section 2. Every pair is $0$-edge-reachable (`SimpleGraph.IsEdgeReachable.zero`), $1$-edge-reachability is reachability (`SimpleGraph.isEdgeReachable_one`), and a graph is $1$-edge-connected if and only if it is preconnected (`SimpleGraph.isEdgeConnected_one`). For a fixed $k$, the relation is an equivalence relation (`SimpleGraph.IsEdgeReachable.refl`, `SimpleGraph.IsEdgeReachable.symm`, `SimpleGraph.IsEdgeReachable.trans`). It is antitone in $k$ (`SimpleGraph.IsEdgeReachable.anti`) and monotone in the graph (`SimpleGraph.IsEdgeReachable.mono`). The step from $k$ to $k + 1$ deletes one edge: `SimpleGraph.isEdgeConnected_add_one` states that for $k \ne 0$, $G$ is $(k+1)$-edge-connected if and only if $G$ minus any edge $e$ is $k$-edge-connected.

**Theorem.** A graph is $2$-edge-connected if and only if it has no bridge.

*Proof.* By `SimpleGraph.isEdgeConnected_two_iff_forall_preconnected`, the graph is $2$-edge-connected when the deletion of any single pair $e$ leaves it preconnected. In Mathlib, `G.IsBridge s(u, v)` means that $u$ and $v$ do not reach each other after the deletion of $s(u, v)$. The definition applies to every unordered pair, also to a pair that is not an edge. If $G$ is $2$-edge-connected, no pair is a bridge, since $G$ minus the pair is preconnected. Conversely, assume that no pair is a bridge. A pair $s(u, v)$ with $u$ and $v$ in different components is a bridge, so $G$ is preconnected. Delete one edge $s(x, y)$. It is not a bridge, so $x$ still reaches $y$, and every walk that used the edge can go around it. So the graph stays preconnected. $\square$

This is `SimpleGraph.isEdgeConnected_two_iff_forall_not_isBridge`, and `SimpleGraph.isBridge_iff_not_isEdgeReachable_two` is the form for one edge. Two vertices on a closed trail are $2$-edge-reachable (`SimpleGraph.Walk.IsTrail.isEdgeReachable_two`), since the trail gives two routes between them with no common edge.

**Theorem.** Let $G$ have at least two vertices. If $G$ is $k$-edge-connected, then each vertex has degree at least $k$.

*Proof.* Let $u$ be a vertex and $v \ne u$ another vertex. Delete the $\deg(u)$ edges at $u$. Then $u$ is isolated and cannot reach $v$. So the deletion of $\deg(u)$ edges disconnects $u$ from $v$, and the definition forces $\deg(u) \ge k$. $\square$

This is `SimpleGraph.IsEdgeConnected.le_degree`, with the pair form `SimpleGraph.IsEdgeReachable.le_degree`. A $k$-edge-connected graph with $k \ne 0$ is preconnected (`SimpleGraph.IsEdgeConnected.preconnected`), and connected on a nonempty type (`SimpleGraph.IsEdgeConnected.connected`). The value $k = \top$ means that no finite set of edges disconnects the graph (`SimpleGraph.isEdgeConnected_top_iff_forall_finite`).

#### Ends of infinite graphs

The module `Mathlib.Combinatorics.SimpleGraph.Ends.Defs` defines the components outside a set $K$ of vertices. The type `G.ComponentCompl K` is the type of connected components of `G.induce Kᶜ`. A vertex $v \notin K$ gives its component `G.componentComplMk h`, and `SimpleGraph.ComponentCompl.supp` is the set of vertices of a component, with the membership lemma `SimpleGraph.ComponentCompl.mem_supp_iff`. The components are nonempty, disjoint from $K$ and pairwise disjoint (`SimpleGraph.ComponentCompl.nonempty`, `SimpleGraph.ComponentCompl.disjoint_right`, `SimpleGraph.ComponentCompl.pairwise_disjoint`). A component is closed under adjacency outside $K$ (`SimpleGraph.ComponentCompl.mem_of_adj`).

A larger set removes more vertices, so its components are smaller. For $K \subseteq L$, each component $C$ outside $L$ lies in exactly one component outside $K$, and `SimpleGraph.ComponentCompl.hom h C` is this component (`SimpleGraph.ComponentCompl.subset_hom`, `SimpleGraph.ComponentCompl.hom_eq_iff_le`). The maps compose (`SimpleGraph.ComponentCompl.hom_trans`). The library packs this as a functor `G.componentComplFunctor : (Finset V)ᵒᵖ ⥤ Type u` from finite sets of vertices, ordered by reverse inclusion, to types. The ends are the sections of this functor: `G.end` is the set of families $(e_K)$, one component $e_K$ outside each finite $K$, with $e_K$ mapped to $e_{K'}$ for $K' \subseteq K$. This is the inverse limit of the sets of components, in the sense of Volume 24, Chapter 2.

The module `Mathlib.Combinatorics.SimpleGraph.Ends.Properties` proves the first facts. Each component of an end is infinite (`SimpleGraph.end_componentCompl_infinite`), and a finite graph has no end (the instance `SimpleGraph.instIsEmptyElemForallObjOppositeFinsetComponentComplFunctorEndOfFinite`). A locally finite preconnected graph has finitely many components outside a finite set (`SimpleGraph.componentCompl_finite`).

**Theorem.** A locally finite, connected, infinite graph has an end.

*Proof sketch.* For each finite $K$ the set of components outside $K$ is finite and nonempty, and at least one of them is infinite. A component outside $K$ is infinite if and only if it contains components outside every larger finite set (`SimpleGraph.ComponentCompl.infinite_iff_in_all_ranges`). So the infinite components form an inverse system of nonempty finite sets with surjective maps. An inverse limit of nonempty finite sets over a directed index is nonempty. This is the compactness argument of the lemma of König on infinite trees, and its element is an end. $\square$

This is `SimpleGraph.nonempty_ends_of_infinite`, with the hypotheses `G.LocallyFinite`, `Fact G.Preconnected` and `Infinite V`. The statements of this module are for a vertex type in `Type`, the lowest universe.

#### Common errors

1. A learner writes `H.Connected` for `H : G.Subgraph` and expects the lemmas of `SimpleGraph.Connected`. The predicate is the structure `SimpleGraph.Subgraph.Connected`, and its field `coe` gives `H.coe.Connected` on the subtype.
2. A learner states `G.IsEdgeConnected k` with `k : ℕ` and meets coercions. The parameter is in `ℕ∞`, and a natural number appears as a cast. Also `G.IsEdgeConnected 0` holds for every graph, and `G.IsEdgeConnected 1` is `G.Preconnected`, which holds on the empty type.
3. A learner expects `G.end` to be a type. It is a set of sections of `G.componentComplFunctor`, and an element of it is a dependent function on `(Finset V)ᵒᵖ` with a proof of compatibility.

### Exercises

1. (A) Show that the cycle $C_n$ with $n \ge 3$ is $2$-edge-connected and not $3$-edge-connected.
2. (A) Find a walk `p` in $K_4$ whose subgraph `p.toSubgraph` is not induced, and name a chord of `p`.
3. (A) Let $V$ have $7$ vertices. Show that every graph on $V$ has an odd component.
4. (B) Show that a graph in which every vertex has even degree has no bridge. Hint: Section 1 of this chapter.
5. (B) Show that the infinite path on $\mathbb{N}$ has one end and the infinite path on $\mathbb{Z}$ has two ends.
6. (C) Show that the infinite grid on $\mathbb{Z}^2$ has exactly one end.

### Reference

<?reference?>
