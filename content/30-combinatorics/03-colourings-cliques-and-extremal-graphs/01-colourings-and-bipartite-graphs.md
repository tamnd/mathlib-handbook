---
title: Colourings and bipartite graphs
kind: theory
modules:
  - Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
  - Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
  - Mathlib.Combinatorics.SimpleGraph.Bipartite
explains:
  E3: [SimpleGraph.Coloring, SimpleGraph.Colorable, SimpleGraph.chromaticNumber, SimpleGraph.IsBipartite, SimpleGraph.chromaticNumber_le_two_iff_isBipartite, SimpleGraph.isBipartite_iff_forall_walk_even_length, SimpleGraph.Walk.three_le_chromaticNumber_of_odd_loop, SimpleGraph.IsBipartite.four_mul_encard_edgeSet_le]
  E2: [SimpleGraph.Coloring.mk, SimpleGraph.Coloring.valid, SimpleGraph.Coloring.colorClass, SimpleGraph.Coloring.colorClasses, SimpleGraph.Coloring.colorClasses_isPartition, SimpleGraph.selfColoring, SimpleGraph.colorable_of_fintype, SimpleGraph.Colorable.mono_left, SimpleGraph.Colorable.of_hom, SimpleGraph.colorable_iff_exists_bdd_nat_coloring, SimpleGraph.colorable_iff_forall_connectedComponent, SimpleGraph.chromaticNumber_le_iff_colorable, SimpleGraph.Colorable.chromaticNumber_le, SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable, SimpleGraph.chromaticNumber_le_card, SimpleGraph.chromaticNumber_top, SimpleGraph.chromaticNumber_top_eq_top_of_infinite, SimpleGraph.chromaticNumber_bot, SimpleGraph.chromaticNumber_eq_card_iff, SimpleGraph.two_le_chromaticNumber_of_adj, SimpleGraph.IsClique.card_le_chromaticNumber, SimpleGraph.cliqueNum_le_chromaticNumber, SimpleGraph.CompleteBipartiteGraph.chromaticNumber, SimpleGraph.chromaticNumber_pathGraph, SimpleGraph.chromaticNumber_cycleGraph_of_odd, SimpleGraph.chromaticNumber_cycleGraph_of_even, SimpleGraph.cycleGraph.tricoloring, SimpleGraph.Coloring.even_length_iff_congr, SimpleGraph.IsBipartiteWith, SimpleGraph.IsBipartiteWith.disjoint, SimpleGraph.IsBipartiteWith.mem_of_adj, SimpleGraph.isBipartite_iff_exists_isBipartiteWith, SimpleGraph.chromaticNumber_eq_two_iff, SimpleGraph.IsBipartiteWith.encard_edgeSet_le, SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges, SimpleGraph.between, SimpleGraph.bipartiteDoubleCover]
  E1: auto
families: []
requires: [V30.C01, V30.C02, V03.C03, V04.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Colourings and bipartite graphs

### Overview

To colour a graph is to give each vertex a colour so that adjacent vertices get different colours. The problem arises whenever conflicting objects must be separated: exams that share a student need different time slots, and radio stations that are close need different frequencies. The chromatic number is the least number of colours that suffices.

This section computes the chromatic numbers of complete graphs, cycles and the Petersen graph, proves that a graph is $2$-colourable if and only if all its closed walks have even length, bounds the number of edges of a bipartite graph, and proves the greedy bound $\chi(G) \le \Delta(G) + 1$.

### Definitions

**Definition (Colouring).** Let $G$ be a graph on $V$ and $\alpha$ a set. A colouring of $G$ with colours in $\alpha$ is a map $c : V \to \alpha$ with $c(u) \neq c(v)$ whenever $u \sim v$. The colour class of $a \in \alpha$ is $c^{-1}(a)$; it contains no edge. The graph is $n$-colourable when it has a colouring with $n$ colours.

**Definition (Chromatic number).** The chromatic number $\chi(G)$ is the least $n$ such that $G$ is $n$-colourable, and $\infty$ if there is no such $n$.

**Definition (Bipartite).** A graph is bipartite when it is $2$-colourable. Equivalently, its vertex set is the union of two disjoint sets $s$ and $t$ such that each edge has one end in $s$ and one in $t$.

::: mathlib
`SimpleGraph.Coloring` · `Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex`

`G.Coloring α` is the type `G →g completeGraph α` of homomorphisms to the complete graph on $\alpha$. Since $a$ and $b$ are adjacent in `completeGraph α` exactly when $a \neq b$, a homomorphism is a map that separates adjacent vertices. `SimpleGraph.Coloring.mk` builds a colouring from a map and a proof, `SimpleGraph.Coloring.valid` extracts the condition, and `SimpleGraph.Coloring.colorClass` and `SimpleGraph.Coloring.colorClasses` give the classes, which form a partition by `SimpleGraph.Coloring.colorClasses_isPartition`. The identity map is a colouring with colours in $V$, `SimpleGraph.selfColoring`.

<?decl SimpleGraph.Coloring?>
:::

::: mathlib
`SimpleGraph.Colorable` · `Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex`

`G.Colorable n` is `Nonempty (G.Coloring (Fin n))`. A finite graph is `Fintype.card V`-colourable by `SimpleGraph.colorable_of_fintype`. A graph is $n$-colourable if and only if each component is, `SimpleGraph.colorable_iff_forall_connectedComponent`, and `SimpleGraph.colorable_iff_exists_bdd_nat_coloring` uses colours in $\mathbb{N}$ below $n$.

<?decl SimpleGraph.Colorable?>
:::

::: mathlib
`SimpleGraph.chromaticNumber` · `Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex`

`G.chromaticNumber : ℕ∞` is the infimum of the $n$ with `G.Colorable n`. If no $n$ works, the infimum of the empty set is `⊤`. The main interface is `SimpleGraph.chromaticNumber_le_iff_colorable`, `G.chromaticNumber ≤ n ↔ G.Colorable n`, with `SimpleGraph.Colorable.chromaticNumber_le` for one direction, and `SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable` for an exact value: `G.chromaticNumber = n + 1 ↔ G.Colorable (n + 1) ∧ ¬G.Colorable n`.

<?decl SimpleGraph.chromaticNumber?>
:::

::: mathlib
`SimpleGraph.IsBipartite` · `Mathlib.Combinatorics.SimpleGraph.Bipartite`

`G.IsBipartite` is an abbreviation for `G.Colorable 2`. The form with sets is `SimpleGraph.IsBipartiteWith G s t`, a structure with the fields `disjoint : Disjoint s t` and `mem_of_adj`, which says that each edge goes between $s$ and $t$. The sets need not cover $V$. The two forms agree by `SimpleGraph.isBipartite_iff_exists_isBipartiteWith`.

<?decl SimpleGraph.IsBipartite?>
:::

### Theorems and proofs

**Proposition (Monotonicity).** If $G \le G'$, then $\chi(G) \le \chi(G')$. More generally, if there is a homomorphism $f : G \to G'$, then a colouring $c$ of $G'$ gives the colouring $c \circ f$ of $G$, so $\chi(G) \le \chi(G')$.

*Proof.* If $u \sim v$ in $G$, then $f(u) \sim f(v)$ in $G'$, so $c(f(u)) \neq c(f(v))$. For $G \le G'$ take $f$ the identity. $\square$

**Proposition (Cliques).** If $G$ has a clique of size $k$, then $\chi(G) \ge k$. In particular $\chi(K_n) = n$, and $\chi(G) \ge 2$ for each graph with an edge.

*Proof.* The vertices of a clique are pairwise adjacent, so a colouring takes $k$ different values on them. For $K_n$, the whole vertex set is a clique of size $n$, and the identity colouring uses $n$ colours. $\square$

::: mathlib
`SimpleGraph.Colorable.of_hom` · `Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex`

`(f : G →g G') → G'.Colorable n → G.Colorable n`, with `SimpleGraph.Colorable.mono_left` for `G ≤ G'`. The bound by cliques is `SimpleGraph.IsClique.card_le_chromaticNumber`, and with the clique number of Section 2 it reads `SimpleGraph.cliqueNum_le_chromaticNumber`. For the complete graph, `SimpleGraph.chromaticNumber_top` gives `Fintype.card V`, `SimpleGraph.chromaticNumber_eq_card_iff` says that only `⊤` attains this value, and `SimpleGraph.chromaticNumber_top_eq_top_of_infinite` gives `⊤` on an infinite type. Also `SimpleGraph.chromaticNumber_bot`, `SimpleGraph.chromaticNumber_le_card` and `SimpleGraph.two_le_chromaticNumber_of_adj`.

<?decl SimpleGraph.Colorable.of_hom?>
:::

**Theorem (Bipartite graphs, König).** A graph $G$ is bipartite if and only if each closed walk in $G$ has even length. For a finite graph this holds if and only if $G$ has no cycle of odd length.

*Proof.* Suppose $c : V \to \{0, 1\}$ is a colouring. Along a walk $v_0, v_1, \ldots, v_k$ the colour changes at each step, so $c(v_i) \equiv c(v_0) + i \pmod 2$. If the walk is closed, then $c(v_k) = c(v_0)$, and $k$ is even.

Conversely, suppose each closed walk has even length. Colour each component separately. In a component $C$ choose a vertex $r$, and for $v \in C$ choose a walk $p_v$ from $r$ to $v$. Put $c(v) = |p_v| \bmod 2$. Let $u \sim v$ in $C$. The walk that follows $p_u$, then the edge from $u$ to $v$, then $p_v$ backwards, is a closed walk at $r$ of length $|p_u| + 1 + |p_v|$. This length is even, so $|p_u|$ and $|p_v|$ have different parities, and $c(u) \neq c(v)$.

For the second statement, a cycle is a closed walk, so one direction is clear. For the other, suppose $G$ has a closed walk of odd length, and choose one, $w = v_0, \ldots, v_k = v_0$, of least length $k$. Then $k \ge 3$, since a walk of length $1$ would be a loop. If two of $v_0, \ldots, v_{k-1}$ are equal, say $v_i = v_j$ with $i < j$, then $w$ splits into the closed walk $v_i, \ldots, v_j$ of length $j - i$ and the closed walk $v_0, \ldots, v_i, v_{j+1}, \ldots, v_k$ of length $k - (j - i)$. Both are shorter than $k$, and one of the lengths is odd, which contradicts the choice. So the vertices $v_0, \ldots, v_{k-1}$ are pairwise different, and a closed walk of length at least $3$ with this property is a cycle. $\square$

::: mathlib
`SimpleGraph.isBipartite_iff_forall_walk_even_length` · `Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions`

`G.IsBipartite ↔ ∀ (v : V) (p : G.Walk v v), Even p.length`. The library proof is the one above: it colours each component by the parity of the length of a chosen walk. The key step is `SimpleGraph.Coloring.even_length_iff_congr`: for a colouring `c` with colours in `Bool` and a walk `p` from `u` to `v`, `Even p.length ↔ (c u = true ↔ c v = true)`. The index of this edition has no declaration for the form with odd cycles; it follows with `SimpleGraph.Walk.IsCycle` and the argument of the last paragraph.

<?decl SimpleGraph.isBipartite_iff_forall_walk_even_length?>
:::

**Corollary (Odd cycles).** If $G$ has a closed walk of odd length, then $\chi(G) \ge 3$. The cycle $C_n$ has $\chi(C_n) = 2$ for even $n$ and $\chi(C_n) = 3$ for odd $n \ge 3$. Paths with at least one edge have chromatic number $2$.

*Proof.* The first statement is the theorem. For $C_n$ with vertices $0, \ldots, n - 1$, the colouring $i \mapsto i \bmod 2$ is valid when $n$ is even, since the last edge joins $n - 1$, which is odd, and $0$. For odd $n$, the cycle is a closed walk of odd length, so $\chi \ge 3$, and the colouring that gives $n - 1$ the colour $2$ and $i \bmod 2$ to the others is valid. A path has no cycle at all, so it is bipartite, and an edge forces two colours. $\square$

::: mathlib
`SimpleGraph.Walk.three_le_chromaticNumber_of_odd_loop` · `Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions`

`(p : G.Walk u u) → Odd p.length → 3 ≤ G.chromaticNumber`. The cycles are `SimpleGraph.cycleGraph n` from `Mathlib.Combinatorics.SimpleGraph.CycleGraph`, with `SimpleGraph.chromaticNumber_cycleGraph_of_odd` and `SimpleGraph.chromaticNumber_cycleGraph_of_even` for $n \ge 2$, and an explicit colouring `SimpleGraph.cycleGraph.tricoloring` with colours in `Fin 3`. For paths there is `SimpleGraph.chromaticNumber_pathGraph`, and for complete bipartite graphs `SimpleGraph.CompleteBipartiteGraph.chromaticNumber`.

<?decl SimpleGraph.Walk.three_le_chromaticNumber_of_odd_loop?>
:::

**Corollary.** $\chi(G) \le 2$ if and only if $G$ is bipartite, and $\chi(G) = 2$ if and only if $G$ is bipartite and has an edge.

*Proof.* The first statement is the definition of the chromatic number, read through $\chi(G) \le n \iff G$ is $n$-colourable. For the second, $\chi(G) \le 1$ means that one colour suffices, that is, $G$ has no edge. $\square$

::: mathlib
`SimpleGraph.chromaticNumber_le_two_iff_isBipartite` · `Mathlib.Combinatorics.SimpleGraph.Bipartite`

`G.chromaticNumber ≤ 2 ↔ G.IsBipartite`, and `SimpleGraph.chromaticNumber_eq_two_iff` is `G.chromaticNumber = 2 ↔ G.IsBipartite ∧ G ≠ ⊥`.

<?decl SimpleGraph.chromaticNumber_le_two_iff_isBipartite?>
:::

**Theorem (Edges of a bipartite graph).** A bipartite graph on $n$ vertices has at most $n^2/4$ edges.

*Proof.* Let $s, t$ be the two colour classes, with $|s| = a$ and $|t| = n - a$. Each edge joins a vertex of $s$ to a vertex of $t$, and different edges give different pairs, so $|E| \le a(n - a)$. Finally $4a(n - a) = n^2 - (n - 2a)^2 \le n^2$. $\square$

The bound is attained by $K_{a, n-a}$ with $a = \lfloor n/2 \rfloor$, which has $\lfloor n^2/4 \rfloor$ edges. Section 2 shows that the same bound holds for all graphs without a triangle.

::: mathlib
`SimpleGraph.IsBipartite.four_mul_encard_edgeSet_le` · `Mathlib.Combinatorics.SimpleGraph.Bipartite`

`G.IsBipartite → 4 * G.edgeSet.encard ≤ ENat.card V ^ 2`. The count is in `ℕ∞`, so the statement also holds for infinite types. The step $|E| \le |s| \cdot |t|$ is `SimpleGraph.IsBipartiteWith.encard_edgeSet_le`. When `s` is a finite set of a bipartition, `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges` counts the edges as the sum of the degrees over `s`. The graph `SimpleGraph.between s t G` keeps the edges of `G` between `s` and `t`, and `SimpleGraph.bipartiteDoubleCover` is the bipartite double cover.

<?decl SimpleGraph.IsBipartite.four_mul_encard_edgeSet_le?>
:::

**Theorem (Greedy colouring).** A finite graph with maximum degree $\Delta$ satisfies $\chi(G) \le \Delta + 1$.

*Proof.* List the vertices as $v_1, \ldots, v_n$, and colour them in this order with colours in $\{0, 1, \ldots, \Delta\}$. When $v_i$ is reached, at most $\deg(v_i) \le \Delta$ of its neighbours already have a colour, so they use at most $\Delta$ of the $\Delta + 1$ colours. Give $v_i$ the least colour that none of them uses. Each edge $v_i v_j$ with $i < j$ is then proper, since $v_j$ avoided the colour of $v_i$. $\square$

The index of this edition has no declaration for the greedy bound $\chi(G) \le \Delta(G) + 1$, and none for the theorem of Brooks, which says that a connected graph other than a complete graph or an odd cycle satisfies $\chi(G) \le \Delta(G)$.

### Examples

**Example (The Petersen graph).** Its vertices are the $2$-subsets of $\{1, \ldots, 5\}$, adjacent when disjoint. The outer five vertices $\{1,2\}, \{3,4\}, \{1,5\}, \{2,3\}, \{4,5\}$ form a cycle of length $5$, so $\chi \ge 3$. For a colouring with three colours, colour $\{i, j\}$ with $i < j$ by $\min(i, 3)$, so by $1$, $2$ or $3$. The pairs of colour $1$ all contain $1$, the pairs of colour $2$ all contain $2$, and the pairs of colour $3$ are the three pairs in $\{3, 4, 5\}$, which pairwise meet. In each class any two pairs meet, so they are not adjacent. Hence $\chi = 3$. The class of colour $1$ has $4$ vertices, the maximum size of an independent set in this graph.

**Example (Complete bipartite graphs).** The graph $K_{m, n}$ with $m, n \ge 1$ has $\chi = 2$: colour one side $0$ and the other $1$. It has $mn$ edges and $m + n$ vertices, and $4mn \le (m + n)^2$ with equality when $m = n$.

**Counterexample (Cliques do not decide).** The cycle $C_5$ has no triangle, so its largest clique has size $2$, but $\chi(C_5) = 3$. The Petersen graph has the same two values. The gap can be arbitrarily large: there are triangle-free graphs of each chromatic number. So the bound of the proposition on cliques is not an equality in general.

### The library around it

`Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex` has the definitions and the general bounds, `Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions` has the parity arguments and the paths and cycles, and `Mathlib.Combinatorics.SimpleGraph.Bipartite` has the bipartitions and the edge bounds. Trees and forests are bipartite by `SimpleGraph.IsTree.isBipartite` of the previous chapter. The Turán graph has a colouring with $r$ colours, `SimpleGraph.Coloring.turanGraph`, used in Section 2.

Common errors of a learner:

- `G.chromaticNumber` lives in `ℕ∞`. A goal `G.chromaticNumber = 3` is a goal in `ℕ∞`; use `SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable` to turn it into two statements about `Colorable`.
- `G.Coloring α` is a homomorphism, so it is applied as a function, `C v`, and the condition is `C.valid`, not a field.
- `G.IsBipartiteWith s t` does not require `s ∪ t = Set.univ`. Isolated vertices may lie outside both sets.

### Exercises

1. (A) Compute the chromatic numbers of the wheel $W_n$, a cycle $C_n$ with one extra vertex adjacent to all others, for even and odd $n$.
2. (A) Show that $\chi(G) \cdot \alpha(G) \ge |V|$, where $\alpha(G)$ is the largest size of an independent set. Deduce $\chi \ge 3$ for the Petersen graph from $\alpha = 4$.
3. (A) Show that $\chi$ of a disjoint union is the maximum of the chromatic numbers.
4. (B) Show that $\chi(G) + \chi(\overline{G}) \le |V| + 1$. Hint: induction on $|V|$.
5. (B) Show that $\chi(G) \cdot \chi(\overline{G}) \ge |V|$.
6. (B) Show that a graph with $m$ edges satisfies $\chi(G)(\chi(G) - 1) \le 2m$.
7. (B) Order the vertices of $C_6$ so that the greedy algorithm uses $3$ colours, and show that some order uses $2$.
8. (C) Show that each finite graph has an order of its vertices for which the greedy algorithm uses exactly $\chi(G)$ colours.
9. (C) Construct the Mycielski graph of $C_5$, the Grötzsch graph on $11$ vertices, and show that it has no triangle and chromatic number $4$.

### Notes and history

The four colour problem, whether the regions of every planar map can be coloured with four colours, was posed by Francis Guthrie in 1852. The proof of Kempe in 1879 had a gap found by Heawood in 1890, and the theorem was proved by Appel and Haken in 1976 with a computer. The characterisation of bipartite graphs by odd cycles is due to König, in his book on graph theory of 1936. Brooks proved his bound in 1941. Mycielski gave triangle-free graphs of each chromatic number in 1955. The headers list Arthur Paulino and Kyle Miller for `Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex`, Iván Renison for `Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions`, and Mitchell Horner for `Mathlib.Combinatorics.SimpleGraph.Bipartite`.

### Reference

<?reference?>
