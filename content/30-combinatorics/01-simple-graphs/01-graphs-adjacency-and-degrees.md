---
title: Graphs, adjacency and degrees
kind: theory
modules:
  - Mathlib.Combinatorics.SimpleGraph.Basic
  - Mathlib.Combinatorics.SimpleGraph.Finite
  - Mathlib.Combinatorics.SimpleGraph.Dart
  - Mathlib.Combinatorics.SimpleGraph.DegreeSum
  - Mathlib.Combinatorics.SimpleGraph.Init
explains:
  E3: [SimpleGraph, SimpleGraph.edgeSet, SimpleGraph.neighborFinset, SimpleGraph.degree, SimpleGraph.Dart, SimpleGraph.sum_degrees_eq_twice_card_edges, SimpleGraph.even_card_odd_degree_vertices]
  E2: [SimpleGraph.Adj, SimpleGraph.neighborSet, SimpleGraph.edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.mem_neighborFinset, SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.Adj.symm, SimpleGraph.Adj.ne, SimpleGraph.fromRel, SimpleGraph.completeGraph, SimpleGraph.emptyGraph, SimpleGraph.top_adj, SimpleGraph.bot_adj, SimpleGraph.compl_adj, SimpleGraph.le_iff_adj, SimpleGraph.edgeSetEmbedding, completeBipartiteGraph, SimpleGraph.LocallyFinite, SimpleGraph.IsRegularOfDegree, SimpleGraph.maxDegree, SimpleGraph.minDegree, SimpleGraph.complete_graph_degree, SimpleGraph.degree_compl, SimpleGraph.card_edgeFinset_top_eq_card_choose_two, SimpleGraph.card_edgeFinset_le_card_choose_two, SimpleGraph.Dart.edge, SimpleGraph.Dart.symm, SimpleGraph.dart_edge_eq_iff, SimpleGraph.dart_card_eq_sum_degrees, SimpleGraph.dart_card_eq_twice_card_edges, SimpleGraph.dart_fst_fiber_card_eq_degree, SimpleGraph.dart_edge_fiber_card, SimpleGraph.odd_card_odd_degree_vertices_ne, SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree]
  E1: auto
families: []
requires: [V03.C03, V03.C04, V03.C06, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Graphs, adjacency and degrees

### Overview

A graph records which pairs of objects are related. The objects are the vertices, and a related pair is an edge. In a simple graph an edge joins two different vertices, and two vertices are joined by at most one edge. So a simple graph on a set $V$ is the same as a relation on $V$ that is symmetric and irreflexive. This section takes that relation as the definition, as Mathlib does, and derives the rest: the edges as unordered pairs, the neighbours of a vertex, and its degree.

The first theorem of graph theory is the degree-sum formula. In a finite graph, the sum of the degrees of the vertices is twice the number of edges. The proof counts the edges with a direction, called darts, in two ways. A corollary is the handshake lemma: the number of vertices of odd degree is even. The section ends with the Petersen graph. It has 10 vertices and 15 edges, and each vertex has degree 3. The next sections compute its distances, its colourings and its cliques.

### Definitions

**Definition (Simple graph).** A simple graph on a set $V$ is a relation $\mathrm{Adj}$ on $V$ such that $\mathrm{Adj}(v, w)$ implies $\mathrm{Adj}(w, v)$, and $\mathrm{Adj}(v, v)$ is false for all $v$. The elements of $V$ are the vertices. When $\mathrm{Adj}(v, w)$ holds, the vertices $v$ and $w$ are adjacent, written $v \sim w$. Then $v \neq w$ by irreflexivity.

An edge is an unordered pair. For $v, w \in V$, write $\{v, w\}$ for the unordered pair, also written $s(v, w)$. The type of unordered pairs of elements of $V$ is the quotient of $V \times V$ by the swap $(v, w) \mapsto (w, v)$. It is called $\mathrm{Sym}^2 V$. Its elements of the form $s(v, v)$ form the diagonal.

**Definition (Edge set).** The edge set of $G$ is the set $E(G) \subseteq \mathrm{Sym}^2 V$ of the pairs $s(v, w)$ with $v \sim w$. This is well defined, since $v \sim w$ if and only if $w \sim v$. No edge lies on the diagonal.

**Definition (Neighbours and degree).** The neighbour set of a vertex $v$ is $N(v) = \{w \in V : v \sim w\}$. When $N(v)$ is finite, the degree of $v$ is $\deg(v) = |N(v)|$. A graph is locally finite when each neighbour set is finite. It is $d$-regular when each vertex has degree $d$. The numbers $\delta(G)$ and $\Delta(G)$ are the minimum and the maximum degree of a finite graph with at least one vertex.

**Definition (Complete and empty graphs).** The complete graph $K_V$ has $v \sim w$ for all $v \neq w$. The empty graph has no edges. The complement $\overline{G}$ has $v \sim w$ if and only if $v \neq w$ and $v \not\sim w$ in $G$. For disjoint sets $A$ and $B$, the complete bipartite graph $K_{A,B}$ on $A \cup B$ has $v \sim w$ exactly when one vertex is in $A$ and the other in $B$.

Graphs on the same set $V$ are ordered: $G \le H$ when each edge of $G$ is an edge of $H$. Under this order the graphs on $V$ form a complete Boolean algebra (Volume 4, Chapter 3). The complete graph is the top $\top$, the empty graph is the bottom $\bot$, the meet and the join are the intersection and the union of the edge sets, and the complement in the algebra is $\overline{G}$. The map $G \mapsto E(G)$ is an order embedding into the subsets of $\mathrm{Sym}^2 V$.

::: mathlib
`SimpleGraph` · `Mathlib.Combinatorics.SimpleGraph.Basic`

The structure `SimpleGraph V` has three fields: the relation `Adj : V → V → Prop`, a proof `symm` that it is symmetric and a proof `loopless` that it is irreflexive. The type `V` can be infinite. For a graph `G`, the statement `G.Adj v w` is the adjacency, `G.Adj.symm` turns it around, and `G.Adj.ne` gives `v ≠ w`. A graph is often built with `SimpleGraph.fromRel r`, whose adjacency is `a ≠ b ∧ (r a b ∨ r b a)`: it makes any relation symmetric and removes the loops. The order is `G ≤ H ↔ ∀ v w, G.Adj v w → H.Adj v w` (`SimpleGraph.le_iff_adj`), and the instance of a complete Boolean algebra gives `⊤`, `⊥`, `⊔`, `⊓` and `Gᶜ`.

<?decl SimpleGraph?>
:::

::: mathlib
`SimpleGraph.edgeSet` · `Mathlib.Combinatorics.SimpleGraph.Basic`

`G.edgeSet : Set (Sym2 V)`, with `SimpleGraph.mem_edgeSet : s(v, w) ∈ G.edgeSet ↔ G.Adj v w`. The type `Sym2 V` of unordered pairs comes from `Mathlib.Data.Sym.Sym2`, outside this volume. The map `SimpleGraph.edgeSetEmbedding` is the order embedding $G \mapsto E(G)$. For counting, `G.edgeFinset` is the edge set as a `Finset`; it needs an instance `Fintype G.edgeSet`, which exists when `V` is finite and the adjacency is decidable.

<?decl SimpleGraph.edgeSet?>
:::

::: mathlib
`SimpleGraph.degree` · `Mathlib.Combinatorics.SimpleGraph.Finite`

`G.neighborSet v : Set V` is $N(v)$. `G.neighborFinset v : Finset V` is the same set as a `Finset`, and `G.degree v : ℕ` is its card (`SimpleGraph.card_neighborFinset_eq_degree`). Both ask for an instance `Fintype (G.neighborSet v)`, so that the degree of a vertex with infinitely many neighbours is never written. The class `G.LocallyFinite` gives this instance for every vertex. In a finite graph, `G.minDegree` and `G.maxDegree` are $\delta$ and $\Delta$, and `G.IsRegularOfDegree d` says that each vertex has degree `d`.

<?decl SimpleGraph.degree?>
:::

**Definition (Dart).** A dart of $G$ is an ordered pair $(v, w)$ with $v \sim w$. Its edge is $s(v, w)$, and its reverse is the dart $(w, v)$. A dart is an edge together with a choice of a direction.

::: mathlib
`SimpleGraph.Dart` · `Mathlib.Combinatorics.SimpleGraph.Dart`

`G.Dart` extends `V × V` with a proof `adj` that the two entries are adjacent. The edge is `d.edge = s(d.fst, d.snd)` (`SimpleGraph.Dart.edge`), and the reverse is `d.symm`. The lemma `SimpleGraph.dart_edge_eq_iff` says that two darts have the same edge if and only if they are equal or reverse to each other. When `V` is finite and the adjacency is decidable, `G.Dart` is a finite type.

<?decl SimpleGraph.Dart?>
:::

### Theorems and proofs

**Lemma (Darts at a vertex).** Let $G$ be locally finite. For each vertex $v$, the number of darts $(v, w)$ that start at $v$ is $\deg(v)$.

*Proof.* The map $(v, w) \mapsto w$ is a bijection from the darts that start at $v$ onto $N(v)$. It is injective, since the dart is determined by its second entry once the first is fixed. It is surjective, since each $w \in N(v)$ gives the dart $(v, w)$. So both sets have $\deg(v)$ elements. $\square$

**Lemma (Darts on an edge).** For each edge $e = s(v, w)$ of $G$, exactly two darts have the edge $e$, namely $(v, w)$ and $(w, v)$.

*Proof.* A dart $(a, b)$ has edge $e$ if and only if $s(a, b) = s(v, w)$, that is $(a, b) = (v, w)$ or $(a, b) = (w, v)$. Both are darts, since $v \sim w$ and $w \sim v$. They are different: if $(v, w) = (w, v)$, then $v = w$, but $v \neq w$ because $v \sim w$. $\square$

**Theorem (Degree-sum formula).** Let $G$ be a graph on a finite set $V$. Then
$$\sum_{v \in V} \deg(v) = 2\,|E(G)|.$$

*Proof.* Let $D$ be the finite set of darts of $G$. Count $D$ by the first entry. The sets of darts that start at the vertices $v$ partition $D$, so by the lemma on darts at a vertex,
$$|D| = \sum_{v \in V} |\{d \in D : d = (v, w) \text{ for some } w\}| = \sum_{v \in V} \deg(v).$$
Count $D$ by the edge. The map $d \mapsto \mathrm{edge}(d)$ goes from $D$ to $E(G)$. Its fibres partition $D$, and by the lemma on darts on an edge each fibre has exactly two elements. So
$$|D| = \sum_{e \in E(G)} 2 = 2\,|E(G)|.$$
The two counts are equal. This is double counting in the form of Volume 3, Chapter 6: the sum over a partition of the sizes of the blocks is the size of the set. $\square$

::: mathlib
`SimpleGraph.sum_degrees_eq_twice_card_edges` · `Mathlib.Combinatorics.SimpleGraph.DegreeSum`

For `[Fintype V] [DecidableRel G.Adj]`, the statement is `∑ v, G.degree v = 2 * #G.edgeFinset`. `SimpleGraph.dart_card_eq_sum_degrees` is the first count, `SimpleGraph.dart_card_eq_twice_card_edges` is the second, and they use `SimpleGraph.dart_fst_fiber_card_eq_degree` and `SimpleGraph.dart_edge_fiber_card` for the sizes of the fibres.

<?decl SimpleGraph.sum_degrees_eq_twice_card_edges?>
:::

**Corollary (Handshake lemma).** In a finite graph, the number of vertices of odd degree is even.

*Proof.* Let $O$ be the set of vertices of odd degree and $P$ the set of vertices of even degree. Then
$$\sum_{v \in O} \deg(v) = 2\,|E(G)| - \sum_{v \in P} \deg(v).$$
The right side is even, since each term of the second sum is even. The left side is a sum of $|O|$ odd numbers, so it has the parity of $|O|$. Hence $|O|$ is even. $\square$

::: mathlib
`SimpleGraph.even_card_odd_degree_vertices` · `Mathlib.Combinatorics.SimpleGraph.DegreeSum`

`Even #{v | Odd (G.degree v)}` for a finite graph with decidable adjacency. The lemma `SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree` says that a vertex of odd degree has a partner $w \neq v$ of odd degree, and `SimpleGraph.odd_card_odd_degree_vertices_ne` states that the odd-degree vertices other than a fixed odd-degree vertex are odd in number.

<?decl SimpleGraph.even_card_odd_degree_vertices?>
:::

**Proposition (Degrees in the complete graph and the complement).** Let $|V| = n$. In $K_V$ each vertex has degree $n - 1$, and $|E(K_V)| = \binom{n}{2}$. For each graph $G$ on $V$, $\deg_{\overline{G}}(v) = n - 1 - \deg_G(v)$, and $|E(G)| \le \binom{n}{2}$.

*Proof.* In $K_V$ the neighbours of $v$ are all vertices other than $v$, so $\deg(v) = n - 1$. By the degree-sum formula, $2|E(K_V)| = n(n-1)$, so $|E(K_V)| = n(n-1)/2 = \binom{n}{2}$. For the complement, the sets $N_G(v)$ and $N_{\overline{G}}(v)$ are disjoint, since $w \sim v$ in $\overline{G}$ means $w \not\sim v$ in $G$. Their union is $V \setminus \{v\}$, since each $w \neq v$ is adjacent to $v$ in exactly one of the two graphs. So $\deg_G(v) + \deg_{\overline{G}}(v) = n - 1$. Finally $G \le K_V$, so $E(G) \subseteq E(K_V)$ and $|E(G)| \le \binom{n}{2}$. $\square$

::: mathlib
`SimpleGraph.card_edgeFinset_top_eq_card_choose_two` · `Mathlib.Combinatorics.SimpleGraph.Finite`

The card of the edge set of `⊤` is `(Fintype.card V).choose 2`. The degree in the complete graph is `SimpleGraph.complete_graph_degree`, equal to `Fintype.card V - 1`, and `SimpleGraph.degree_compl` gives `Gᶜ.degree v = Fintype.card V - 1 - G.degree v`. The bound for any graph is `SimpleGraph.card_edgeFinset_le_card_choose_two`. The subtraction is the truncated subtraction of `ℕ`. It is exact here, since `G.degree v ≤ Fintype.card V - 1`.

<?decl SimpleGraph.card_edgeFinset_top_eq_card_choose_two?>
:::

### Examples

**Example (The Petersen graph).** Let $V$ be the set of 2-element subsets of $\{1, 2, 3, 4, 5\}$, so $|V| = \binom{5}{2} = 10$. Two vertices are adjacent when they are disjoint. This graph is the Petersen graph $P$.

Degrees. The vertex $\{1, 2\}$ is disjoint from exactly the 2-subsets of $\{3, 4, 5\}$, which are $\{3, 4\}$, $\{3, 5\}$ and $\{4, 5\}$. So $\deg(\{1,2\}) = 3$. The same count works for any vertex $\{a, b\}$: its neighbours are the $\binom{3}{2} = 3$ subsets of the complement. So $P$ is 3-regular. By the degree-sum formula, $2|E(P)| = 10 \cdot 3 = 30$, and $|E(P)| = 15$.

The complement. In $\overline{P}$ two different 2-subsets are adjacent when they meet in one element. By the proposition, $\overline{P}$ is 6-regular, since $10 - 1 - 3 = 6$, and it has $45 - 15 = 30$ edges.

Common neighbours. Two adjacent vertices, say $\{1,2\}$ and $\{3,4\}$, have no common neighbour: a common neighbour avoids $\{1,2,3,4\}$, so it lies in $\{5\}$, which has no 2-subset. Two non-adjacent vertices, say $\{1,2\}$ and $\{1,3\}$, have exactly one common neighbour: it avoids $\{1,2,3\}$, so it is $\{4,5\}$. These two facts give the diameter in Chapter 2 and the triangle-free property in Chapter 3.

The index of this edition has no declaration for the Petersen graph. It can be defined as `SimpleGraph.fromRel` of the relation `Disjoint` on the 2-element finsets of `Fin 5`.

**Example (Degree sequences that do not occur).** No finite graph has exactly one vertex of odd degree. For instance, there is no graph on 5 vertices with degrees $3, 2, 2, 2, 2$: the sum $11$ is odd, but the degree-sum formula makes it even. In the same way there is no 3-regular graph on 7 vertices, since $7 \cdot 3 = 21$ is odd. A $d$-regular graph on $n$ vertices needs $nd$ even, and then it has $nd/2$ edges.

**Counterexample (Infinite degree).** Let $V = \mathbb{N}$ and let $0 \sim n$ for all $n \ge 1$, with no other edges. The vertex $0$ has infinitely many neighbours, so its degree is not defined as a natural number. The graph is not locally finite. In Mathlib the term `G.degree 0` cannot be formed here, because no instance `Fintype (G.neighborSet 0)` exists.

### The library around it

The file `Mathlib.Combinatorics.SimpleGraph.Basic` works for any type of vertices, and `Mathlib.Combinatorics.SimpleGraph.Finite` adds the `Finset` forms. The membership lemma for the neighbour finset is `SimpleGraph.mem_neighborFinset`. The adjacency of the top and the bottom is `SimpleGraph.top_adj` (`v ≠ w`) and `SimpleGraph.bot_adj` (`False`), and the adjacency of the complement is `SimpleGraph.compl_adj`. The graphs `SimpleGraph.completeGraph` and `SimpleGraph.emptyGraph` are abbreviations for `⊤` and `⊥`, and `completeBipartiteGraph V W` lives on the sum type `V ⊕ W`.

Common errors of a learner:

- `G.degree v` needs an instance `Fintype (G.neighborSet v)`. When the type `V` is finite, this instance comes from `Fintype V` and `DecidableRel G.Adj`. A goal that shows two different instances is solved by `convert` or by `Fintype.card_congr`, not by `rfl`.
- An edge `s(v, w)` and the pair `(v, w)` are different objects. The equation `s(v, w) = s(w, v)` holds, and `Sym2.mk_eq_mk_iff` says when two unordered pairs are equal.
- The degree of the complement is stated with the subtraction of `ℕ`, which stops at `0`. Before a rewrite with `SimpleGraph.degree_compl`, check that the bound `G.degree v < Fintype.card V` is at hand.

### Exercises

1. (A) List the neighbours of $\{2, 5\}$ in the Petersen graph, and show that no two of them are adjacent. Hint: the neighbours are 2-subsets of a 3-element set.
2. (A) Show that a graph on $n \ge 2$ vertices has two vertices of the same degree. Hint: the degrees lie in $\{0, \ldots, n-1\}$, and $0$ and $n-1$ cannot both occur. Use the pigeonhole principle of Volume 3.
3. (A) Show that $K_n$ is $(n-1)$-regular and that a $d$-regular graph on $n$ vertices has $nd/2$ edges.
4. (A) Find the degrees and the number of edges of the complement of $K_{a,b}$.
5. (B) Show that $\delta(G) \le 2|E(G)|/|V| \le \Delta(G)$ for a finite graph with at least one vertex.
6. (B) For each even $n \ge 4$, build a 3-regular graph on $n$ vertices. Hint: start from a cycle on $n$ vertices and add the edges between opposite vertices.
7. (B) Let $G$ be a graph on $n$ vertices with $\delta(G) \ge (n-1)/2$. Show that any two non-adjacent vertices have a common neighbour. Hint: count $|N(v)| + |N(w)|$ inside $V \setminus \{v, w\}$.
8. (C) Show that the Petersen graph has exactly 120 automorphisms. Hint: each permutation of $\{1, \ldots, 5\}$ gives an automorphism. For the upper bound, show that an automorphism is determined by the images of one vertex, of its three neighbours and of one more vertex, and count the choices as $10 \cdot 6 \cdot 2$.
9. (C) Show that the Petersen graph contains no cycle of length 3 or 4. Hint: use the counts of common neighbours from the example.

### Notes and history

Euler's paper of 1736 on the bridges of Königsberg is the usual start of graph theory, and it contains the parity argument behind the handshake lemma. The Petersen graph is named after Julius Petersen, who used it in 1898 as an example of a 3-regular graph without a decomposition into three perfect matchings. It had appeared earlier in work of Kempe. The book of Holton and Sheehan, *The Petersen Graph* (1993), collects its properties. The file headers of `Mathlib.Combinatorics.SimpleGraph.Basic` list Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov and Hunter Monroe as authors, and the header of `Mathlib.Combinatorics.SimpleGraph.DegreeSum` lists Kyle Miller. Diestel, *Graph Theory*, Chapter 1, and Bollobás, *Modern Graph Theory*, Chapter 1, give the material of this section.

### Reference

<?reference?>
