---
title: Maps, decompositions and traversal of walks
kind: api
modules:
  - Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
  - Mathlib.Combinatorics.SimpleGraph.Walk.Maps
  - Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
  - Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
  - Mathlib.Combinatorics.SimpleGraph.Walk.Counting
  - Mathlib.Combinatorics.SimpleGraph.Walk.Chord
explains:
  E2: [SimpleGraph.Walk.adj_getVert_succ, SimpleGraph.Walk.length_map, SimpleGraph.Walk.take_spec, SimpleGraph.Walk.count_support_takeUntil_eq_one, SimpleGraph.Walk.isSubwalk_antisymm, SimpleGraph.walkLengthTwoEquivCommonNeighbors, SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  E1: auto
families: []
requires: [V30.C01, V03.C02, V03.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Maps, decompositions and traversal of walks

### Overview

Section 1 of this chapter defines a walk as an inductive object: the empty walk `nil` at a vertex, or one step `cons` followed by a walk. That section also gives the length, the support, the edges, the reverse and the concatenation of walks. A proof about walks needs more tools than these. It must read the $i$-th vertex of a walk, move a walk from one graph to another, cut a walk at a vertex, compare a walk with a piece of another walk, and count the walks of a given length. The six modules of this section hold these tools.

The modules are an API, and the mathematics in them is simple. The difficulty is the form of the statements. A walk `p : G.Walk u v` has its two ends in its type, so an operation that changes an end must change the type. The library solves this with dependent types and with the function `SimpleGraph.Walk.copy`, which rewrites the ends along equalities. This section explains the families of lemmas and the choices behind them. Sections 5 and 6 of this chapter use these tools for Hamiltonian cycles, girth and connected subgraphs.

### The library around it

#### The vertices of a walk by position

The module `Mathlib.Combinatorics.SimpleGraph.Walk.Traversal` reads a walk position by position. For a walk $p = (v_0, v_1, \ldots, v_n)$ the value `p.getVert i` is $v_i$. The function is total: for $i \ge n$ it returns the last vertex $v_n$ (`SimpleGraph.Walk.getVert_of_length_le`). The two ends are `SimpleGraph.Walk.getVert_zero` and `SimpleGraph.Walk.getVert_length`. The link with the list of vertices is `SimpleGraph.Walk.getVert_eq_support_getElem`: for $i \le n$, `p.getVert i = p.support[i]`.

**Theorem.** For $i < n$, the vertices $v_i$ and $v_{i+1}$ are adjacent.

*Proof.* Induction on the walk. For `nil` the length is $0$ and no $i$ exists. For `cons h q` with $h : u \sim w$, the case $i = 0$ is the edge $h$ itself, since $v_0 = u$ and $v_1 = w$. For $i = j + 1$ the rule `SimpleGraph.Walk.getVert_cons_succ` gives $v_{j+1} = q_j$ and $v_{j+2} = q_{j+1}$, and the induction hypothesis for $q$ applies. $\square$

This is `SimpleGraph.Walk.adj_getVert_succ`. The second vertex and the vertex before the end have short names: `p.snd` is $v_1$ and `p.penultimate` is $v_{n-1}$. They are adjacent to the ends when the walk is not empty: `SimpleGraph.Walk.adj_snd` and `SimpleGraph.Walk.adj_penultimate` take the hypothesis `¬p.Nil`. The first and the last darts, `p.firstDart hp` and `p.lastDart hp`, also need this hypothesis, since an empty walk has no dart. Their edges are $s(v_0, v_1)$ and $s(v_{n-1}, v_n)$ (`SimpleGraph.Walk.edge_firstDart`, `SimpleGraph.Walk.edge_lastDart`). The functions `SimpleGraph.Walk.tail` and `SimpleGraph.Walk.dropLast` remove the first and the last step, and `SimpleGraph.Walk.take` and `SimpleGraph.Walk.drop` cut at a position.

#### Walks along maps of graphs

The module `Mathlib.Combinatorics.SimpleGraph.Walk.Maps` moves walks between graphs. The basic map is `SimpleGraph.Walk.map`: a homomorphism `f : G →g G'` sends a walk from $u$ to $v$ in $G$ to a walk from $f(u)$ to $f(v)$ in $G'$. It sends each vertex to its image and each edge to the image edge.

**Theorem.** A homomorphism keeps the length of a walk.

*Proof.* Induction on the walk. The map sends `nil` to `nil` (`SimpleGraph.Walk.map_nil`) and `cons h p` to `cons (f.map_adj h) (p.map f)` (`SimpleGraph.Walk.map_cons`). So each step gives one step. $\square$

This is `SimpleGraph.Walk.length_map`. The other parts of a walk map as lists:

| Lean name | Statement |
|---|---|
| `SimpleGraph.Walk.support_map` | the support of `p.map f` is `p.support.map f` |
| `SimpleGraph.Walk.edges_map` | the edges are `p.edges.map (Sym2.map f)` |
| `SimpleGraph.Walk.darts_map` | the darts are the image darts |
| `SimpleGraph.Walk.map_append` | the map of `p.append q` is the append of the maps |
| `SimpleGraph.Walk.reverse_map` | the map commutes with the reverse |
| `SimpleGraph.Walk.map_map` | `(p.map f).map f' = p.map (f'.comp f)` |
| `SimpleGraph.Walk.map_id` | the identity map does nothing |

When $f$ is injective on vertices, `SimpleGraph.Walk.map_injective_of_injective` makes the map of walks injective, and `SimpleGraph.Walk.IsPath.map` keeps paths. A homomorphism that is not injective can send a path to a walk with a repeated vertex.

Three special maps change only the graph and keep the vertex type. The first is `SimpleGraph.Walk.mapLe h p` for `h : G ≤ G'`, the map along the inclusion of graphs. Its support and its edges are those of `p` (`SimpleGraph.Walk.support_mapLe_eq_support`, `SimpleGraph.Walk.edges_mapLe_eq_edges`). The second is `p.transfer H hp`. It moves `p` into any graph `H` that contains the edges of `p`, with no relation between $G$ and $H$. When $G \le H$ it agrees with `mapLe` (`SimpleGraph.Walk.transfer_eq_mapLe`). The third is `SimpleGraph.Walk.toDeleteEdges s p hp`, which moves `p` into `G.deleteEdges s` when no edge of `p` lies in `s`, and `SimpleGraph.Walk.toDeleteEdge` is the case of one edge. Finally, `SimpleGraph.Walk.induce s p hp` moves a walk with all its vertices in `s` into the induced graph `G.induce s` on the subtype, with `SimpleGraph.Walk.length_induce` and `SimpleGraph.Walk.support_induce`.

#### Cutting a walk at a vertex

The module `Mathlib.Combinatorics.SimpleGraph.Walk.Decomp` cuts a walk at the first visit to a vertex. Let `p : G.Walk v w` and let $u$ be a vertex of `p`, with the proof `h : u ∈ p.support`. Then `p.takeUntil u h : G.Walk v u` is the part of `p` up to the first visit to $u$, and `p.dropUntil u h : G.Walk u w` is the rest. Both need `DecidableEq V`, since the definition tests each vertex against $u$.

**Theorem.** The two parts give back the walk: `(p.takeUntil u h).append (p.dropUntil u h) = p`.

*Proof.* Induction on `p`. If `p` is `nil`, then $u = v$ and both parts are `nil`. If `p` is `cons h' q` with first vertex $v$, there are two cases. When $u = v$, `takeUntil` is `nil` and `dropUntil` is all of `p`. When $u \neq v$, the vertex $u$ is in the support of `q`, `takeUntil` is `cons h'` followed by `q.takeUntil u`, and `dropUntil` is `q.dropUntil u`. The induction hypothesis for `q` closes the case. $\square$

This is `SimpleGraph.Walk.take_spec`. The same induction shows that the first part visits $u$ only once, at its end.

**Theorem.** The vertex $u$ occurs exactly once in the support of `p.takeUntil u h`.

*Proof.* In the induction above, the first part ends at the first occurrence of $u$ in the support of `p`. Every earlier vertex differs from $u$. $\square$

This is `SimpleGraph.Walk.count_support_takeUntil_eq_one`. The parts are shorter than the whole (`SimpleGraph.Walk.length_takeUntil_le_length`, `SimpleGraph.Walk.length_dropUntil_le_length`), and strictly shorter when $u$ is not the far end (`SimpleGraph.Walk.length_takeUntil_lt_length`). Their supports, darts and edges are prefixes and suffixes of those of `p`: examples are `SimpleGraph.Walk.support_takeUntil_subset_support`, `SimpleGraph.Walk.edges_takeUntil_prefix_edges` and `SimpleGraph.Walk.darts_dropUntil_suffix_darts`. The forms with positions are `SimpleGraph.Walk.takeUntil_eq_take` and `SimpleGraph.Walk.dropUntil_eq_drop`: `takeUntil` is `take` at the index of the first occurrence of $u$, up to `copy`.

A closed walk can start at any of its vertices. For `c : G.Walk v v` and a vertex $u$ of `c`, the walk `c.rotate u h : G.Walk u u` is the same closed walk started at $u$. It is `dropUntil` followed by `takeUntil`. It has the same length (`SimpleGraph.Walk.length_rotate`), and its edges and darts are a rotation of the old lists (`SimpleGraph.Walk.rotate_edges`, `SimpleGraph.Walk.rotate_darts`). The relation `~r` of these lemmas is `List.IsRotated`, not equality. The statement `SimpleGraph.Walk.mem_support_iff_exists_append` gives the cut without decidability: $u$ is a vertex of `p` if and only if `p` is an append of a walk to $u$ and a walk from $u$.

#### Subwalks

The module `Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks` defines `p.IsSubwalk q`: the walk `p` is a contiguous piece of `q`. The definition asks for walks `ru` and `rv` with `q = (ru.append p).append rv`. The ends of `p` and `q` can differ, so the relation lives on walks with any ends. It is reflexive and transitive (`SimpleGraph.Walk.isSubwalk_rfl`, `SimpleGraph.Walk.IsSubwalk.trans`), and a subwalk is at most as long as the walk (`SimpleGraph.Walk.length_le_of_isSubwalk`).

**Theorem.** Two walks with the same ends that are subwalks of each other are equal.

*Proof.* Let `p₁` be a subwalk of `p₂` and `p₂` a subwalk of `p₁`. The lengths satisfy $\ell(p_1) \le \ell(p_2) \le \ell(p_1)$, so they are equal. In the decomposition `p₂ = (ru.append p₁).append rv` the length of `p₂` is $\ell(ru) + \ell(p_1) + \ell(rv)$. So `ru` and `rv` have length $0$, they are `nil`, and `p₂ = p₁`. $\square$

This is `SimpleGraph.Walk.isSubwalk_antisymm`. For a walk that is not empty, the relation is the infix relation on the lists of darts (`SimpleGraph.Walk.isSubwalk_iff_darts_isInfix`), and it implies the infix relation on supports and edges (`SimpleGraph.Walk.IsSubwalk.edges_isInfix`, `SimpleGraph.Walk.IsSubwalk.support_subset`). An edge $s(u', v')$ lies on `p` if and only if the one step walk of this edge, in one of its two directions, is a subwalk of `p` (`SimpleGraph.Walk.isSubwalk_toWalk_iff_mem_edges`). The pieces of a walk are subwalks: `SimpleGraph.Walk.isSubwalk_takeUntil`, `SimpleGraph.Walk.isSubwalk_dropUntil`, `SimpleGraph.Walk.isSubwalk_take`, `SimpleGraph.Walk.isSubwalk_drop`. A map of graphs keeps the relation (`SimpleGraph.Walk.IsSubwalk.map`).

#### Counting walks

The module `Mathlib.Combinatorics.SimpleGraph.Walk.Counting` makes the sets of walks of a given length finite. For a locally finite graph, `G.finsetWalkLength n u v` is the finset of walks from $u$ to $v$ of length $n$, with `SimpleGraph.mem_finsetWalkLength_iff`. Its definition follows the recursion `SimpleGraph.Walk.setOfPred_length_eq_add_one`: a walk of length $n + 1$ from $u$ is a step to a neighbour $w$ followed by a walk of length $n$ from $w$. The card of the set of such walks is the card of this finset (`SimpleGraph.card_set_walk_length_eq`). Chapter 1 computes the same number as an entry of a power of the adjacency matrix, with `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`. The variant `G.finsetWalkLengthLT n u v` holds the walks of length less than $n$, and the instances `SimpleGraph.fintypeSetPathLength` and `SimpleGraph.Path.instFintype` give finitely many paths. A path in a finite graph has length less than the number of vertices, so the set of all paths is finite.

**Theorem.** The walks of length $2$ from $u$ to $v$ are in bijection with the common neighbours of $u$ and $v$.

*Proof.* A walk of length $2$ is $u, w, v$ with $u \sim w$ and $w \sim v$. The middle vertex $w$ is a common neighbour. Conversely a common neighbour $w$ gives the walk $u, w, v$. The two maps are inverse to each other. $\square$

This is the equivalence `SimpleGraph.walkLengthTwoEquivCommonNeighbors`, with `SimpleGraph.walkLengthTwoEquivCommonNeighbors_apply_coe` for the middle vertex. It gives the diagonal and the off-diagonal entries of $A^2$ in Chapter 1.

#### Chords

The module `Mathlib.Combinatorics.SimpleGraph.Walk.Chord` defines the chords of a walk. An edge $e$ of $G$ is a chord of `p` when both ends of $e$ are vertices of `p` and $e$ is not an edge of `p` (`SimpleGraph.Walk.IsChord`, with the unfolded form `SimpleGraph.Walk.isChord_sym2Mk`). A walk is chordless when it has no chord (`SimpleGraph.Walk.IsChordless`).

**Theorem.** A walk `p` is chordless if and only if each edge of $G$ between two vertices of `p` is an edge of `p`.

*Proof.* A chord is an edge between two vertices of `p` that is not an edge of `p`. So "no chord" is the statement that each such edge is an edge of `p`. $\square$

This is `SimpleGraph.Walk.isChordless_iff_forall_mem_edges`, and `SimpleGraph.Walk.IsChordless.mem_edges` is its forward direction. A one step walk is chordless (`SimpleGraph.Adj.isChordless_toWalk`). An embedding of graphs keeps chordless walks and reflects them (`SimpleGraph.Walk.isChordless_map_iff`), and the same holds for chords (`SimpleGraph.Walk.isChord_map_iff`). A homomorphism that is not an embedding can add a chord. Section 6 of this chapter shows that a walk is chordless if and only if the subgraph that it spans is induced. A chordless cycle is an induced cycle, and a chordless path is an induced path.

#### Common errors

1. A learner uses `p.takeUntil u h` in a context with no `DecidableEq V`. The term does not elaborate. Add `[DecidableEq V]` or `classical`, and expect the lemmas to carry the same instance.
2. A learner states a fact about `p.getVert i` for all $i$ and forgets the junk value. For $i$ beyond the length, `p.getVert i` is the last vertex, and a statement such as `SimpleGraph.Walk.adj_getVert_succ` needs `i < p.length`.
3. A learner expects `(c.rotate u h).edges = c.edges`. The edges are only a rotation of the list. Use the lemmas with `~r` and the invariance of `List.IsRotated` under length, membership and count.

### Exercises

1. (A) Let `p` be the walk $1, 2, 3, 4$ in the path graph on $\{1, 2, 3, 4\}$. Compute `p.getVert 2`, `p.getVert 7`, `p.snd`, `p.penultimate`, `p.takeUntil 3 h` and `p.dropUntil 3 h`.
2. (A) Show that a subwalk of a path is a path, from `SimpleGraph.Walk.IsSubwalk.support_subset` and the infix relation on supports.
3. (A) Give a homomorphism $f$ of graphs and a path $p$ such that `p.map f` is not a path.
4. (B) Show that the number of walks of length $2$ from $u$ to $u$ is the degree of $u$, from `SimpleGraph.walkLengthTwoEquivCommonNeighbors`.
5. (B) Let $c$ be a closed walk and $u$ a vertex of $c$. Show that `c.rotate u h` is a cycle if and only if $c$ is a cycle.
6. (C) Show that a shortest cycle of a graph is chordless. Deduce that a graph with a cycle has a chordless cycle.

### Reference

<?reference?>
