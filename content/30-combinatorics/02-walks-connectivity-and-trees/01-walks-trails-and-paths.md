---
title: Walks, trails and paths
kind: theory
modules:
  - Mathlib.Combinatorics.SimpleGraph.Walk.Basic
  - Mathlib.Combinatorics.SimpleGraph.Walk.Operations
  - Mathlib.Combinatorics.SimpleGraph.Paths
  - Mathlib.Combinatorics.SimpleGraph.Trails
explains:
  E3: [SimpleGraph.Walk, SimpleGraph.Walk.IsTrail, SimpleGraph.Walk.IsPath, SimpleGraph.Walk.IsCycle, SimpleGraph.Walk.bypass, SimpleGraph.Walk.IsEulerian, SimpleGraph.Walk.IsEulerian.even_degree_iff, SimpleGraph.Walk.IsEulerian.card_odd_degree]
  E2: [SimpleGraph.Walk.nil, SimpleGraph.Walk.cons, SimpleGraph.Walk.length, SimpleGraph.Walk.support, SimpleGraph.Walk.edges, SimpleGraph.Walk.darts, SimpleGraph.Walk.append, SimpleGraph.Walk.reverse, SimpleGraph.Walk.concat, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_edges, SimpleGraph.Walk.edges_subset_edgeSet, SimpleGraph.Walk.IsCircuit, SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.bypass_isPath, SimpleGraph.Walk.length_bypass_le_length, SimpleGraph.Walk.support_bypass_subset_support, SimpleGraph.Walk.edges_bypass_subset_edges, SimpleGraph.Walk.toPath, SimpleGraph.Path, SimpleGraph.Walk.IsPath.length_lt, SimpleGraph.Walk.IsTrail.length_le_card_edgeFinset, SimpleGraph.Walk.IsCircuit.three_le_length, SimpleGraph.Walk.isEulerian_iff, SimpleGraph.Walk.IsEulerian.isTrail, SimpleGraph.Walk.IsEulerian.edgeSet_eq, SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem, SimpleGraph.Walk.IsTrail.even_countP_edges_iff, SimpleGraph.Walk.IsEulerian.connected_of_forall_not_isIsolated]
  E1: auto
families: []
requires: [V30.C01, V03.C03, V03.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Walks, trails and paths

### Overview

A walk moves along the edges of a graph, one step at a time. It may use a vertex or an edge many times. A trail uses each edge at most once, a path uses each vertex at most once, and a cycle is a closed trail that returns to its start without other repeated vertices. These notions measure how a graph is connected, and Sections 2 and 3 build on them.

This section defines walks as Mathlib does, by induction, and derives the length, the vertices and the edges of a walk. It proves that a walk from $u$ to $v$ contains a path from $u$ to $v$. It then proves the theorem of Euler on trails that use every edge once. In a finite graph with such a trail, the number of vertices of odd degree is $0$ or $2$. Conversely, a finite connected graph with all degrees even has a closed trail through every edge. The index of this edition has the first statement and no declaration for the converse. The section proves both.

### Definitions

**Definition (Walk).** Let $G$ be a graph on $V$. The walks of $G$ from $u$ to $w$ are defined by two rules. For each vertex $u$ there is the empty walk $\mathrm{nil}_u$ from $u$ to $u$. If $u \sim v$ and $p$ is a walk from $v$ to $w$, then $\mathrm{cons}(h, p)$ is a walk from $u$ to $w$, where $h$ is the proof of $u \sim v$. Each walk arises from these rules in finitely many steps.

A walk is thus a sequence $u = v_0, v_1, \ldots, v_n = w$ with $v_{i-1} \sim v_i$ for each $i$. Its length is the number $n$ of steps. Its support is the list $(v_0, \ldots, v_n)$ of $n+1$ vertices. Its edges are the list of the $n$ edges $s(v_{i-1}, v_i)$, and its darts are the list of the $n$ darts $(v_{i-1}, v_i)$. A walk is closed when $u = w$.

The reverse of $v_0, \ldots, v_n$ is $v_n, \ldots, v_0$. The append $p \cdot q$ of a walk $p$ from $u$ to $v$ and a walk $q$ from $v$ to $w$ is $p$ followed by $q$.

**Definition (Trail, path, circuit, cycle).** A walk is a trail when its list of edges has no repetition. It is a path when its support has no repetition. A circuit is a closed trail of positive length. A cycle is a circuit $v_0, v_1, \ldots, v_n = v_0$ in which $v_1, \ldots, v_n$ are pairwise different.

A path is a trail: if an edge $s(a, b)$ appeared twice, then $a$ or $b$ would appear twice in the support. A cycle has length at least $3$: a circuit of length $1$ would be a loop, and a circuit $v_0, v_1, v_0$ of length $2$ would use the edge $s(v_0, v_1)$ twice.

**Definition (Eulerian trail).** A walk is Eulerian when it uses each edge of $G$ exactly once. An Eulerian walk is a trail. An Eulerian circuit is a closed Eulerian trail.

::: mathlib
`SimpleGraph.Walk` · `Mathlib.Combinatorics.SimpleGraph.Walk.Basic`

`G.Walk u v` is the inductive type with constructors `Walk.nil : G.Walk u u` and `Walk.cons : G.Adj u v → G.Walk v w → G.Walk u w`. The data are `p.length : ℕ`, `p.support : List V`, `p.edges : List (Sym2 V)` and `p.darts : List G.Dart`. The basic counts are `SimpleGraph.Walk.length_support` (`p.support.length = p.length + 1`) and `SimpleGraph.Walk.length_edges`. `SimpleGraph.Walk.edges_subset_edgeSet` says that the edges of a walk are edges of `G`.

<?decl SimpleGraph.Walk?>
:::

The operations are in `Mathlib.Combinatorics.SimpleGraph.Walk.Operations`: `p.reverse : G.Walk v u`, `p.append q : G.Walk u w`, and `p.concat h`, which adds one step at the end. Their lengths are `SimpleGraph.Walk.length_reverse` and `SimpleGraph.Walk.length_append`.

::: mathlib
`SimpleGraph.Walk.IsTrail` · `Mathlib.Combinatorics.SimpleGraph.Paths`

`p.IsTrail` is a structure with the field `edges_nodup : p.edges.Nodup` (`SimpleGraph.Walk.isTrail_def`). `p.IsCircuit` adds `p ≠ nil` for a closed walk, and `SimpleGraph.Walk.IsCircuit.three_le_length` gives the bound $3 \le n$. `SimpleGraph.Walk.IsTrail.length_le_card_edgeFinset` bounds the length of a trail by the number of edges.

<?decl SimpleGraph.Walk.IsTrail?>
:::

::: mathlib
`SimpleGraph.Walk.IsPath` · `Mathlib.Combinatorics.SimpleGraph.Paths`

`p.IsPath` extends `p.IsTrail` with `support_nodup`, and `SimpleGraph.Walk.isPath_def` says `p.IsPath ↔ p.support.Nodup`. The type `G.Path u v` is the subtype of walks that are paths. `SimpleGraph.Walk.IsPath.length_lt` gives `p.length < Fintype.card V` on a finite type.

<?decl SimpleGraph.Walk.IsPath?>
:::

::: mathlib
`SimpleGraph.Walk.IsCycle` · `Mathlib.Combinatorics.SimpleGraph.Paths`

`p.IsCycle` for `p : G.Walk u u` extends `p.IsCircuit` with `support_nodup : p.support.tail.Nodup`, and `SimpleGraph.Walk.isCycle_def` unfolds it. The tail drops the first vertex, which equals the last. `SimpleGraph.Walk.cons_isCycle_iff` says that `cons h p` is a cycle if and only if `p` is a path and the edge of `h` is not an edge of `p`.

<?decl SimpleGraph.Walk.IsCycle?>
:::

### Theorems and proofs

**Theorem (Walks contain paths).** If $G$ has a walk from $u$ to $v$, then it has a path from $u$ to $v$ whose vertices and edges are among those of the walk, and whose length is at most the length of the walk.

*Proof.* Among the walks from $u$ to $v$ whose vertices and edges are among those of the given walk, choose one, $p = (v_0, \ldots, v_n)$, of least length. Suppose a vertex repeats: $v_i = v_j$ with $i < j$. Then $v_0, \ldots, v_i, v_{j+1}, \ldots, v_n$ is again a walk from $u$ to $v$, since $v_i = v_j \sim v_{j+1}$. Its vertices and edges are among those of $p$, and its length is $n - (j - i) < n$. This contradicts the choice of $p$. So $p$ is a path. $\square$

The library constructs such a path by a recursion instead of a choice. The bypass of $\mathrm{cons}(h, p)$, with $h : u \sim v$, first computes the bypass $p'$ of $p$. If $u$ lies in the support of $p'$, the result is the part of $p'$ after the occurrence of $u$. Otherwise it is $\mathrm{cons}(h, p')$.

::: mathlib
`SimpleGraph.Walk.bypass` · `Mathlib.Combinatorics.SimpleGraph.Paths`

`p.bypass : G.Walk u v`, for `[DecidableEq V]`. The theorem is `SimpleGraph.Walk.bypass_isPath`, with `SimpleGraph.Walk.length_bypass_le_length`, `SimpleGraph.Walk.support_bypass_subset_support` and `SimpleGraph.Walk.edges_bypass_subset_edges`. `p.toPath : G.Path u v` packs the bypass with the proof that it is a path.

<?decl SimpleGraph.Walk.bypass?>
:::

**Lemma (Parity of a trail at a vertex).** Let $p$ be a trail from $u$ to $v$ and $x$ a vertex. Let $c(x)$ be the number of edges of $p$ that contain $x$. If $u = v$, then $c(x)$ is even. If $u \neq v$, then $c(x)$ is odd for $x \in \{u, v\}$ and even for the other vertices.

*Proof.* Write $p = (v_0, \ldots, v_n)$. Each edge $s(v_{i-1}, v_i)$ of $p$ has two different ends, and the edges are pairwise different. For each $i$ let $e_i = s(v_{i-1}, v_i)$. An occurrence $v_k = x$ with $0 < k < n$ is the end of the two edges $e_k$ and $e_{k+1}$. An occurrence with $k = 0$ or $k = n$ is the end of one edge, if $n > 0$. Each edge that contains $x$ is counted once in this way, at the occurrence of $x$ at one of its ends, since an edge has two different ends and only one of them is $x$. So $c(x)$ is the sum over the occurrences of $x$ of $2$ for an inner occurrence and $1$ for an end occurrence. If $n = 0$, then $c(x) = 0$ and $u = v$. Let $n > 0$. If $u = v$, then the two end occurrences belong to the same vertex and add $2$ to $c(u)$, so every $c(x)$ is even. If $u \neq v$, the vertex $u$ gets $1$ from $k = 0$ and $v$ gets $1$ from $k = n$, so $c(u)$ and $c(v)$ are odd and all others are even. $\square$

**Theorem (Euler, necessity).** Let $G$ be finite and let $p$ be an Eulerian trail from $u$ to $v$. Then $\deg(x)$ is even for each $x$ if $u = v$. If $u \neq v$, then $\deg(x)$ is odd exactly for $x \in \{u, v\}$. In both cases, the number of vertices of odd degree is $0$ or $2$.

*Proof.* The trail uses each edge exactly once, so the edges of $p$ that contain $x$ are all the edges at $x$, and $c(x) = \deg(x)$. The lemma gives the parities. $\square$

::: mathlib
`SimpleGraph.Walk.IsEulerian.even_degree_iff` · `Mathlib.Combinatorics.SimpleGraph.Trails`

`p.IsEulerian → (Even (G.degree w) ↔ (u ≠ v → w ≠ u ∧ w ≠ v))`. The definition `p.IsEulerian` is `∀ e ∈ G.edgeSet, p.edges.count e = 1`, and `SimpleGraph.Walk.isEulerian_iff` rewrites it as a trail that contains every edge. The parity lemma is `SimpleGraph.Walk.IsTrail.even_countP_edges_iff`. `SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem` builds an Eulerian trail from a trail through every edge, and `SimpleGraph.Walk.IsEulerian.edgeSet_eq` says that its edge set is the edge set of `G`.

<?decl SimpleGraph.Walk.IsEulerian.even_degree_iff?>
:::

::: mathlib
`SimpleGraph.Walk.IsEulerian.card_odd_degree` · `Mathlib.Combinatorics.SimpleGraph.Trails`

The number of odd-degree vertices of a graph with an Eulerian trail is `0` or `2`. The header of the file lists the converse as a task for the future, and the index of this edition has no declaration for it. A related fact is `SimpleGraph.Walk.IsEulerian.connected_of_forall_not_isIsolated`: if a graph has an Eulerian trail and no isolated vertex, it is connected.

<?decl SimpleGraph.Walk.IsEulerian.card_odd_degree?>
:::

For the converse, call $G$ connected when any two vertices are joined by a walk. Section 2 studies this notion.

**Theorem (Euler, sufficiency).** Let $G$ be a finite connected graph with at least one edge, in which every vertex has even degree. Then $G$ has an Eulerian circuit.

*Proof.* Trails have length at most $|E(G)|$, so there is a trail $p = (v_0, \ldots, v_n)$ of greatest length. Since $G$ has an edge, $n \ge 1$.

Step 1: $p$ is closed. Suppose $v_0 \neq v_n$. By the parity lemma, an odd number of edges of $p$ contain $v_n$. But $\deg(v_n)$ is even, so some edge $s(v_n, y)$ is not an edge of $p$. Then $p$ followed by the step to $y$ is a longer trail, a contradiction.

Step 2: $p$ uses every edge. Let $S$ be the set of vertices of $p$. Suppose some vertex $x \in S$ lies on an edge $s(x, y)$ that $p$ does not use. Since $p$ is closed, it can be read from any of its vertices: if $x = v_k$, then $v_k, v_{k+1}, \ldots, v_n = v_0, v_1, \ldots, v_k$ is a closed trail with the same edges. Followed by the step to $y$, it is a trail of length $n + 1$, a contradiction. So every edge at a vertex of $S$ is an edge of $p$. Suppose now that some edge $s(a, b)$ is not an edge of $p$. Then $a \notin S$. By connectivity there is a walk from $v_0$ to $a$. It starts in $S$ and ends outside $S$, so one of its steps goes from a vertex of $S$ to a vertex outside $S$. That edge is not an edge of $p$, since both ends of an edge of $p$ lie in $S$. This contradicts the first part of Step 2. So $p$ uses every edge, once each, and it is an Eulerian circuit. $\square$

**Corollary.** A finite connected graph with exactly two vertices $u \neq v$ of odd degree has an Eulerian trail from $u$ to $v$.

*Proof.* Add a new vertex $z$ with the two edges $s(u, z)$ and $s(z, v)$. The new graph is connected, $z$ has degree $2$, and $u$ and $v$ now have even degree. By the theorem it has an Eulerian circuit. Read the circuit from $z$: it has the form $z, u, \ldots, v, z$ or $z, v, \ldots, u, z$, since the only edges at $z$ go to $u$ and $v$. Removing $z$ leaves a trail between $u$ and $v$ through every edge of $G$. Reverse it if needed. $\square$

### Examples

**Example (The complete graph $K_5$).** Each vertex of $K_5$ has degree $4$, so $K_5$ has an Eulerian circuit. One is
$$1, 2, 3, 4, 5, 1, 3, 5, 2, 4, 1.$$
Its ten edges are $12, 23, 34, 45, 51, 13, 35, 52, 24, 41$. They are pairwise different, and there are $\binom{5}{2} = 10$ edges in all. For $K_n$ the degree is $n - 1$, so $K_n$ has an Eulerian circuit exactly when $n$ is odd. The graph $K_4$ has four vertices of odd degree, so it has no Eulerian trail.

**Example (The bridges of Königsberg).** The town had four land masses $A, B, C, D$ and seven bridges: two between $A$ and $B$, two between $A$ and $C$, and one each between $A$ and $D$, $B$ and $D$, $C$ and $D$. Two bridges join the same pair of masses, so the bridges are not the edges of a simple graph. Put a new vertex in the middle of each bridge. The result is a simple graph with $4 + 7 = 11$ vertices and $14$ edges. The new vertices have degree $2$, and the masses have degrees $\deg A = 5$, $\deg B = 3$, $\deg C = 3$ and $\deg D = 3$. So four vertices have odd degree, and by the necessity theorem there is no walk that crosses each bridge exactly once.

**Counterexample (A closed walk that contains no cycle).** In the path $a \sim b$, the walk $a, b, a$ is closed of length $2$. It is not a trail, since it uses $s(a, b)$ twice. A closed walk need not contain a cycle, while a closed trail of positive length always contains one (Exercise 6).

### The library around it

Many lemmas about walks are proved by `induction p` with the two cases `nil` and `cons`, and `simp` knows the lengths, the supports and the edges of the operations.

Common errors of a learner:

- The ends of a walk are indices of its type. A walk `p : G.Walk u v` cannot be compared with a walk `q : G.Walk u w` by `=` without a proof of `v = w` and `Walk.copy`.
- `p.support` is a list, not a set. Membership `x ∈ p.support` is list membership, and `p.support.Nodup` is the statement that no vertex repeats.
- `IsCycle` asks for `p.support.tail.Nodup`, not `p.support.Nodup`. The full support of a closed walk always repeats its first vertex at the end.
- `IsEulerian` needs `DecidableEq V`, since it counts edges in a list.

### Exercises

1. (A) Write the walk $1, 2, 3, 1$ in $K_3$ with `nil` and `cons`, and compute its support, its edges and its length.
2. (A) Show that the reverse of a trail is a trail and that the reverse of a path is a path.
3. (A) Give a graph and a trail in it that is not a path.
4. (A) For which $m, n \ge 1$ does the complete bipartite graph $K_{m,n}$ have an Eulerian circuit? An Eulerian trail that is not closed?
5. (B) Show that the append of two trails need not be a trail, and that the append of a path from $u$ to $v$ and a path from $v$ to $w$ contains a path from $u$ to $w$.
6. (B) Show that each circuit contains a cycle. Hint: among the closed pieces $v_i, \ldots, v_j$ with $i < j$ and $v_i = v_j$, take one of least length.
7. (B) Let $G$ be finite with $\delta(G) \ge 2$. Show that $G$ contains a cycle. Hint: take a longest path $v_0, \ldots, v_k$ and look at the neighbours of $v_k$.
8. (B) Show that a finite connected graph with $2k$ vertices of odd degree, $k \ge 1$, has $k$ trails that together use every edge exactly once. Hint: add $k$ new vertices, each joined to two of the odd vertices, and use the sufficiency theorem.
9. (C) Show that the edge set of a finite graph with all degrees even is a disjoint union of the edge sets of cycles. Hint: Exercise 7 applied to the graph without its isolated vertices.

### Notes and history

Euler solved the problem of the bridges of Königsberg in a paper written in 1736. He showed that a walk over each bridge once needs at most two land masses with an odd number of bridges. He stated the converse without proof. Hierholzer proved the converse in a paper published in 1873, after his death, and the proof by a longest trail above is close to his. In Mathlib the file `Mathlib.Combinatorics.SimpleGraph.Trails` has the necessary direction, and its header lists the converse as future work. The headers of `Mathlib.Combinatorics.SimpleGraph.Paths` and `Mathlib.Combinatorics.SimpleGraph.Trails` list Kyle Miller, and the header of `Mathlib.Combinatorics.SimpleGraph.Walk.Basic` lists Kyle Miller and Peter Nelson.

### Reference

<?reference?>
