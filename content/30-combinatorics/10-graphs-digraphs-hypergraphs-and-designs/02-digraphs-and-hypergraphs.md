---
title: Digraphs and hypergraphs
kind: api
modules:
  - Mathlib.Combinatorics.Digraph.Basic
  - Mathlib.Combinatorics.Digraph.Orientation
  - Mathlib.Combinatorics.Hypergraph.Basic
explains:
  E2: [Digraph.adj_injective, Digraph.completeAtomicBooleanAlgebra, Digraph.toSimpleGraphStrict_subgraph_toSimpleGraphInclusive, Digraph.toSimpleGraphInclusive_mono, Hypergraph.sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated, Hypergraph.isLoop_iff_mem_and_ncard_one, Hypergraph.ne_bot_iff, Hypergraph.IsComplete.not_isTrivial, Hypergraph.IsTrivial.isLinear, Hypergraph.image_image]
  E1: auto
families: []
requires: [V30.C01, V03.C03, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Digraphs and hypergraphs

### Overview

This section describes two generalizations of the simple graphs of Chapter 1. A digraph drops the two conditions on the adjacency relation: it need not be symmetric, and it can have loops. A hypergraph keeps the symmetry but lets an edge contain any number of vertices.

The two types use different designs. `Digraph V` is a relation on the whole type `V`, like `SimpleGraph V`, so the digraphs on `V` form a complete Boolean algebra. `Hypergraph α` uses embedded sets, like `Graph α β` of Section 1: a hypergraph has a vertex set in `α` and a set of edges, and each edge is a subset of the vertex set.

### The library around it

#### Digraphs as relations

The structure `Digraph` has the single field `Digraph.Adj : V → V → Prop`. The statement `G.Adj v w` says that there is an arc from $v$ to $w$. There are no axioms, so `G.Adj v v` is allowed and `G.Adj v w` does not give `G.Adj w v`. The type `Digraph V` carries the same data as `Quiver.{0} V`, the quivers with arrows in `Prop`. The difference is in use. `Quiver` is a class, so one quiver structure is attached to a type. A term of `Digraph V` is one element of the lattice of all digraphs on `V`.

The digraph is fixed by its relation, and this is `Digraph.adj_injective`. So each order structure on relations passes to digraphs. The order `G ≤ H` is `Digraph.IsSubgraph`: each arc of $G$ is an arc of $H$ (`Digraph.isSubgraph_eq_le`). This is the order of spanning subgraphs, because all digraphs on `V` have the vertex type `V`.

| Lean name | Statement |
|---|---|
| `Digraph.sup_adj` | $(G \sqcup H).\mathrm{Adj}\ v\ w \iff G.\mathrm{Adj}\ v\ w \vee H.\mathrm{Adj}\ v\ w$ |
| `Digraph.inf_adj` | $(G \sqcap H).\mathrm{Adj}\ v\ w \iff G.\mathrm{Adj}\ v\ w \wedge H.\mathrm{Adj}\ v\ w$ |
| `Digraph.sdiff_adj` | $(G \setminus H).\mathrm{Adj}\ v\ w \iff G.\mathrm{Adj}\ v\ w \wedge \neg H.\mathrm{Adj}\ v\ w$ |
| `Digraph.compl_adj` | $G^c.\mathrm{Adj}\ v\ w \iff \neg G.\mathrm{Adj}\ v\ w$ |
| `Digraph.sSup_adj` | an arc of $\bigsqcup s$ is an arc of some $G \in s$ |
| `Digraph.sInf_adj` | an arc of $\bigsqcap s$ is an arc of each $G \in s$ |
| `Digraph.top_adj` | each pair $(v, w)$ is an arc of $\top$, including $v = w$ |
| `Digraph.bot_adj` | $\bot$ has no arc |

The indexed forms are `Digraph.iSup_adj` and `Digraph.iInf_adj`.

**Theorem.** `Digraph V` is a complete atomic Boolean algebra.

*Proof.* The map $G \mapsto G.\mathrm{Adj}$ is injective, and each operation in the table is the pointwise operation on relations $V \to V \to \mathrm{Prop}$. So `Digraph V` is isomorphic to the power set of $V \times V$, with the arcs as the elements. A power set is a complete atomic Boolean algebra, and its atoms are the singletons. $\square$

This is the instance `Digraph.completeAtomicBooleanAlgebra`. The distributive lattice structure alone is the instance `Digraph.distribLattice`. The atoms are the digraphs with one arc. Note the difference with `SimpleGraph V`: there, the top element is the complete graph without loops, and the complement of $G$ has no loops.

The named digraphs are `Digraph.completeDigraph V`, equal to $\top$, `Digraph.emptyDigraph V`, equal to $\bot$, and `Digraph.completeBipartiteGraph V W` on `V ⊕ W`. The last one has an arc between two vertices if and only if they are on different sides, in both directions. The function `Digraph.mk'` builds a digraph from a Boolean relation. It is an embedding, and it gives the instance `Fintype (Digraph V)` for a finite type `V` with decidable equality. So there are $2^{|V|^2}$ digraphs on a finite `V`.

#### Forgetting the orientation

The module `Mathlib.Combinatorics.Digraph.Orientation` turns a digraph into a simple graph in two ways.

| Lean name | Edge $\{v, w\}$ present when |
|---|---|
| `Digraph.toSimpleGraphInclusive` | $v \ne w$ and an arc $v \to w$ or $w \to v$ exists |
| `Digraph.toSimpleGraphStrict` | $v \ne w$ and both arcs $v \to w$ and $w \to v$ exist |

The inclusive form is `SimpleGraph.fromRel G.Adj` from Chapter 1, so `SimpleGraph.fromRel_adj` unfolds it. Both maps remove the loops.

**Theorem.** For each digraph $G$, the strict graph of $G$ is a subgraph of the inclusive graph of $G$. Both maps are monotone.

*Proof.* If $v \ne w$ and both arcs exist, then one arc exists. If $G \le H$, then each arc of $G$ is an arc of $H$, so each condition in the table for $G$ gives the same condition for $H$. $\square$

These are `Digraph.toSimpleGraphStrict_subgraph_toSimpleGraphInclusive`, `Digraph.toSimpleGraphInclusive_mono` and `Digraph.toSimpleGraphStrict_mono`. The maps send $\top$ to $\top$ and $\bot$ to $\bot$ (`Digraph.toSimpleGraphInclusive_top`, `Digraph.toSimpleGraphStrict_top`, `Digraph.toSimpleGraphInclusive_bot`, `Digraph.toSimpleGraphStrict_bot`). The library has no map in the other direction yet, from a simple graph to its orientations.

#### Hypergraphs

The structure `Hypergraph` has the fields `Hypergraph.vertexSet`, with the notation `V(H)`, and `Hypergraph.edgeSet`, with the notation `E(H)`. An edge is a term of `Set α`, and the axiom says that each edge is a subset of $V(H)$ (`Hypergraph.subset_vertexSet_of_mem_edgeSet`). The edge set is a set and not a multiset, so a hypergraph has no repeated edges. Two hypergraphs with the same vertex sets and edge sets are equal (`Hypergraph.ext`).

| Lean name | Statement |
|---|---|
| `Hypergraph.edgeSet_subset_powerset_vertexSet` | $E(H) \subseteq \mathcal{P}(V(H))$ |
| `Hypergraph.mem_vertexSet_of_mem_edgeSet` | a point of an edge is a vertex |
| `Hypergraph.sUnion_edgeSet_subset_vertexSet` | $\bigcup E(H) \subseteq V(H)$ |
| `Hypergraph.edgeSet.ext_iff` | two edges are equal if they have the same vertices |

Two vertices $x$ and $y$ are adjacent (`Hypergraph.Adj`) if some edge contains both. This relation is symmetric (`Hypergraph.Adj.symm`, `Hypergraph.adj_comm`). Two edges $e$ and $f$ are adjacent (`Hypergraph.EAdj`) if both are edges and some point is in both. Then $e \cap f$ is nonempty (`Hypergraph.EAdj.inter_nonempty`).

A vertex $x$ is isolated (`Hypergraph.IsIsolated`) if no edge contains it.

**Theorem.** $\bigcup E(H) = V(H)$ if and only if no vertex of $H$ is isolated.

*Proof.* The inclusion $\bigcup E(H) \subseteq V(H)$ always holds. So the equality says that each vertex is in some edge, which is the negation of isolation for each $x \in V(H)$. $\square$

This is `Hypergraph.sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated`.

An edge $e$ is a loop (`Hypergraph.IsLoop`) if it is an edge and $e = \{x\}$ for some $x$. By `Hypergraph.isLoop_iff_mem_and_ncard_one`, this is the same as $e \in E(H)$ with `Set.ncard e = 1`. The proof is the characterization of the sets of cardinality one as singletons. Note that `Hypergraph.Adj x x` holds for each $x$ in some edge, loop or not.

#### Special hypergraphs

The bottom hypergraph $\bot$ has no vertices and no edges. A hypergraph is nonempty (`Hypergraph.IsNonempty`) if $V(H)$ or $E(H)$ is nonempty.

**Theorem.** $H \ne \bot$ if and only if `H.IsNonempty`.

*Proof.* If $V(H)$ and $E(H)$ are both empty, then $H = \bot$ by `Hypergraph.ext`. Conversely, $\bot$ has empty vertex and edge sets. $\square$

This is `Hypergraph.ne_bot_iff`, and `Hypergraph.not_isNonempty_iff` is the negated form. The definition uses both sets, because an edge of a hypergraph can be the empty set. So $E(H)$ can be nonempty when $V(H)$ is empty.

A hypergraph is trivial (`Hypergraph.IsTrivial`) if $V(H)$ is nonempty and $E(H)$ is empty. The constructor `Hypergraph.trivialOn s` has the vertex set $s$ and no edges, and it is trivial when $s$ is nonempty (`Hypergraph.IsTrivial.trivialOn`). A hypergraph is complete (`Hypergraph.IsComplete`) if each subset of $V(H)$ is an edge. The constructor `Hypergraph.completeOn s` has the vertex set $s$ and the edge set $\mathcal{P}(s)$ (`Hypergraph.mem_completeOn`).

**Theorem.** A complete hypergraph is not trivial.

*Proof.* The empty set is a subset of $V(H)$, so it is an edge of a complete $H$. So $E(H)$ is not empty. $\square$

This is `Hypergraph.IsComplete.not_isTrivial`. The same argument gives `Hypergraph.IsComplete.isNonempty`, also for $V(H) = \emptyset$.

A hypergraph is linear (`Hypergraph.IsLinear`) if two distinct edges meet in at most one point. The form with `Set.Pairwise` is `Hypergraph.isLinear_def`, and `Hypergraph.IsLinear.inter_subsingleton` applies the condition to two edges. A simple graph, seen as a hypergraph with edges of size two, is linear. A trivial hypergraph is linear, because it has no edges (`Hypergraph.IsTrivial.isLinear`).

#### Images

For $f : \alpha \to \beta$, the image `H.image f` has the vertex set $f(V(H))$ and the edges $f(e)$ for $e \in E(H)$ (`Hypergraph.mem_edgeSet_image`, `Hypergraph.image_mem_edgeSet_image`). Two edges with the same image become one edge, because the edge set has no repeated elements.

**Theorem.** $(H.\mathrm{image}\ f).\mathrm{image}\ g = H.\mathrm{image}\ (g \circ f)$.

*Proof.* Both vertex sets are $g(f(V(H))) = (g \circ f)(V(H))$. An edge on the left is $g(f(e))$ for some $e \in E(H)$, and $g(f(e)) = (g \circ f)(e)$. So both edge sets are the same. $\square$

This is `Hypergraph.image_image`.

#### Common errors

1. A learner proves a statement about `⊤ : Digraph V` and expects no loops, as for `SimpleGraph`. The arc $v \to v$ is in $\top$ for each $v$ (`Digraph.top_adj`). Use `Digraph.toSimpleGraphInclusive` to remove the loops.
2. A learner expects the empty set never to be an edge of a hypergraph. The type allows $\emptyset \in E(H)$, and `Hypergraph.completeOn s` always has it. A statement about the edges may need the hypothesis that each edge is nonempty.
3. A learner uses `Hypergraph.IsIsolated H x` as a statement about a vertex. The definition has no condition $x \in V(H)$, so each point outside $V(H)$ is isolated too.

### Exercises

1. (A) Let $V = \{1, 2, 3\}$ and let $G$ have the arcs $1 \to 2$, $2 \to 1$, $2 \to 3$ and $3 \to 3$. Compute `G.toSimpleGraphInclusive` and `G.toSimpleGraphStrict`.
2. (A) Count the digraphs on a set of $n$ elements, and the digraphs without loops.
3. (A) Show that `(G ⊔ H).toSimpleGraphInclusive` is the join of the two inclusive graphs. Is the same statement true for the strict graphs?
4. (B) Show that `Hypergraph.completeOn s` is linear if and only if $s$ has at most two elements.
5. (B) Let $H$ have the vertex set $\{1, 2, 3, 4\}$ and the edges $\{1, 2\}$ and $\{3, 4\}$, and let $f$ send $1, 3$ to $a$ and $2, 4$ to $b$. Compute `H.image f`, and show that the image has fewer edges than $H$.
6. (C) A Steiner triple system on $V$ is a linear hypergraph with $V(H) = V$ in which each edge has three elements and each pair of distinct vertices is in some edge. Show that $|V| \equiv 1$ or $3 \pmod 6$ when $|V| \ge 1$ is finite, and give the example with $|V| = 7$.

### Reference

<?reference?>
