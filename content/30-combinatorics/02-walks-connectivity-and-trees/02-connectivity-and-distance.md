---
title: Connectivity and distance
kind: theory
modules:
  - Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
  - Mathlib.Combinatorics.SimpleGraph.Metric
  - Mathlib.Combinatorics.SimpleGraph.Diam
explains:
  E3: [SimpleGraph.Reachable, SimpleGraph.Connected, SimpleGraph.ConnectedComponent, SimpleGraph.connected_or_connected_compl, SimpleGraph.edist, SimpleGraph.dist, SimpleGraph.eccent, SimpleGraph.ediam, SimpleGraph.diam]
  E2: [SimpleGraph.Preconnected, SimpleGraph.Reachable.refl, SimpleGraph.Reachable.symm, SimpleGraph.Reachable.trans, SimpleGraph.Reachable.elim_path, SimpleGraph.Reachable.map, SimpleGraph.Adj.reachable, SimpleGraph.reachable_is_equivalence, SimpleGraph.reachableSetoid, SimpleGraph.reachable_iff_reflTransGen, SimpleGraph.connected_iff, SimpleGraph.connected_iff_exists_forall_reachable, SimpleGraph.Connected.preconnected, SimpleGraph.Connected.map, SimpleGraph.Preconnected.mono, SimpleGraph.connected_top, SimpleGraph.connected_bot_iff, SimpleGraph.reachable_or_reachable_compl, SimpleGraph.connectedComponentMk, SimpleGraph.ConnectedComponent.eq, SimpleGraph.ConnectedComponent.sound, SimpleGraph.ConnectedComponent.exact, SimpleGraph.ConnectedComponent.ind, SimpleGraph.ConnectedComponent.supp, SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.map, SimpleGraph.Iso.connectedComponentEquiv, SimpleGraph.Walk.exists_boundary_dart, SimpleGraph.Reachable.exists_walk_length_eq_dist, SimpleGraph.dist_le, SimpleGraph.edist_le, SimpleGraph.dist_comm, SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable, SimpleGraph.dist_eq_one_iff_adj, SimpleGraph.edist_triangle, SimpleGraph.Connected.dist_triangle, SimpleGraph.edist_eq_top_of_not_reachable, SimpleGraph.radius, SimpleGraph.center, SimpleGraph.mem_center_iff, SimpleGraph.radius_le_ediam, SimpleGraph.ediam_le_two_mul_radius, SimpleGraph.ediam_le_iff, SimpleGraph.eccent_le_iff, SimpleGraph.edist_le_ediam, SimpleGraph.dist_le_diam, SimpleGraph.connected_iff_ediam_ne_top, SimpleGraph.ediam_eq_top_of_not_connected, SimpleGraph.ediam_eq_one, SimpleGraph.diam_top, SimpleGraph.diam_bot, SimpleGraph.center_nonempty]
  E1: auto
families: []
requires: [V30.C01, V03.C03, V04.C01, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Connectivity and distance

### Overview

Two vertices are in the same piece of a graph when a walk joins them. This relation is an equivalence relation, and its classes are the connected components. A graph is connected when it has exactly one component. Section 1 used connectivity in the proof of the theorem of Euler, through a criterion proved here: a graph is connected if and only if every split of the vertices into two nonempty parts has an edge across.

On a connected graph, the length of a shortest walk is a metric. This section defines the distance, the eccentricity of a vertex, the radius and the diameter, and proves that the diameter is at most twice the radius. Its main example is the Petersen graph, which has diameter $2$ although each vertex has only $3$ neighbours. Section 1 of this chapter is assumed.

### Definitions

**Definition (Reachability).** Let $G$ be a graph on $V$. A vertex $v$ is reachable from $u$ when $G$ has a walk from $u$ to $v$. The graph is preconnected when any two vertices are reachable from each other. It is connected when it is preconnected and $V$ is nonempty.

The empty type is preconnected but not connected. The reason is the same as for topological spaces: a connected graph should have exactly one component, and the empty graph on no vertices has none.

**Definition (Connected component).** The connected components of $G$ are the classes of the equivalence relation of reachability (the proposition below proves that it is one). The component of $v$ is written $C(v)$. The support of a component is its set of vertices.

::: mathlib
`SimpleGraph.Reachable` · `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`

`G.Reachable u v` is `Nonempty (G.Walk u v)`. It is a proposition, so it forgets the walk. To get a walk back inside a proof of a proposition, use `SimpleGraph.Reachable.elim`, or `SimpleGraph.Reachable.elim_path` for a path. The lemma `SimpleGraph.reachable_iff_reflTransGen` identifies reachability with the reflexive and transitive closure of `G.Adj`, and `SimpleGraph.Reachable.map` says that a homomorphism keeps it.

<?decl SimpleGraph.Reachable?>
:::

::: mathlib
`SimpleGraph.Connected` · `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`

`G.Preconnected` is `∀ u v, G.Reachable u v`. `G.Connected` is a structure with the fields `preconnected` and `nonempty : Nonempty V`. It is a structure and not a conjunction so that `hG u v` can be written for `hG : G.Connected`, through a coercion to a function. The lemmas `SimpleGraph.connected_iff` and `SimpleGraph.connected_iff_exists_forall_reachable` give the two usual forms, and `SimpleGraph.Connected.map` says that the image under a surjective homomorphism is connected.

<?decl SimpleGraph.Connected?>
:::

::: mathlib
`SimpleGraph.ConnectedComponent` · `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`

`G.ConnectedComponent` is the quotient `Quot G.Reachable`, and `G.connectedComponentMk v` is the class of `v`. The key lemma is `SimpleGraph.ConnectedComponent.eq`: two classes are equal if and only if the vertices are reachable. Its two directions are `ConnectedComponent.sound` and `ConnectedComponent.exact`. `C.supp : Set V` is the support, with `SimpleGraph.ConnectedComponent.mem_supp_iff`. Proofs about all components use `SimpleGraph.ConnectedComponent.ind`, which reduces to the class of one vertex.

<?decl SimpleGraph.ConnectedComponent?>
:::

**Definition (Distance).** The extended distance $d(u, v) \in \mathbb{N} \cup \{\infty\}$ is the least length of a walk from $u$ to $v$, and $\infty$ when no walk exists. The eccentricity of $u$ is $e(u) = \sup_v d(u, v)$. The diameter is $\operatorname{diam} G = \sup_u e(u)$, and the radius is $\operatorname{rad} G = \inf_u e(u)$. The center is the set of vertices $u$ with $e(u) = \operatorname{rad} G$.

::: mathlib
`SimpleGraph.edist` · `Mathlib.Combinatorics.SimpleGraph.Metric`

`G.edist u v : ℕ∞` is the infimum of the lengths of the walks from `u` to `v`. The infimum of the empty set in `ℕ∞` is `⊤`, so `SimpleGraph.edist_eq_top_of_not_reachable` holds by definition. The bound `SimpleGraph.edist_le` compares with any walk, and `SimpleGraph.edist_triangle` holds without any hypothesis, since `⊤` absorbs.

<?decl SimpleGraph.edist?>
:::

::: mathlib
`SimpleGraph.dist` · `Mathlib.Combinatorics.SimpleGraph.Metric`

`G.dist u v : ℕ` is `(G.edist u v).toNat`, so it is `0` for unreachable vertices. Hence `SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable` has two cases, and the triangle inequality `SimpleGraph.Connected.dist_triangle` needs a connected graph. `SimpleGraph.Reachable.exists_walk_length_eq_dist` gives a walk of the least length, and `SimpleGraph.dist_eq_one_iff_adj` characterises the adjacent pairs.

<?decl SimpleGraph.dist?>
:::

::: mathlib
`SimpleGraph.eccent` · `Mathlib.Combinatorics.SimpleGraph.Diam`

`G.eccent u : ℕ∞` is `⨆ v, G.edist u v`. The radius `G.radius` is `⨅ u, G.eccent u`, the center `G.center` is `{u | G.eccent u = G.radius}`, and `SimpleGraph.mem_center_iff` unfolds it. The bound by a constant is `SimpleGraph.eccent_le_iff`.

<?decl SimpleGraph.eccent?>
:::

::: mathlib
`SimpleGraph.ediam` · `Mathlib.Combinatorics.SimpleGraph.Diam`

`G.ediam : ℕ∞` is `⨆ u, G.eccent u`. The library proves `SimpleGraph.ediam_le_iff`, `SimpleGraph.edist_le_ediam`, `SimpleGraph.radius_le_ediam` and `SimpleGraph.ediam_le_two_mul_radius`. On a finite nonempty type, `SimpleGraph.connected_iff_ediam_ne_top` says that a graph is connected if and only if its diameter is finite, and `SimpleGraph.ediam_eq_top_of_not_connected` is one direction.

<?decl SimpleGraph.ediam?>
:::

::: mathlib
`SimpleGraph.diam` · `Mathlib.Combinatorics.SimpleGraph.Diam`

`G.diam : ℕ` is `G.ediam.toNat`. It is `0` for a disconnected graph, as `SimpleGraph.diam_bot` shows for the empty graph. `SimpleGraph.dist_le_diam` needs the hypothesis `G.ediam ≠ ⊤`. On at least two vertices, `SimpleGraph.ediam_eq_one` says that the diameter is $1$ exactly for the complete graph, and `SimpleGraph.diam_top` computes it.

<?decl SimpleGraph.diam?>
:::

### Theorems and proofs

**Proposition (Reachability is an equivalence relation).** For all vertices, $u$ is reachable from $u$; if $v$ is reachable from $u$, then $u$ is reachable from $v$; and if $v$ is reachable from $u$ and $w$ from $v$, then $w$ is reachable from $u$.

*Proof.* The empty walk $\mathrm{nil}_u$ goes from $u$ to $u$. The reverse of a walk from $u$ to $v$ goes from $v$ to $u$. The append of a walk from $u$ to $v$ and a walk from $v$ to $w$ goes from $u$ to $w$. $\square$

Each vertex lies in exactly one component, and an edge $s(v, w)$ has both ends in the same component, since the one-step walk joins them. So the graph is the disjoint union of the induced subgraphs on its components, with no edges between them.

**Theorem (Connectivity by cuts).** A graph $G$ on a nonempty set $V$ is connected if and only if for each set $S$ with $\emptyset \neq S \neq V$ there is an edge $s(a, b)$ with $a \in S$ and $b \notin S$.

*Proof.* Suppose $G$ is connected, and let $S$ be such a set. Choose $u \in S$ and $v \notin S$, and a walk $v_0 = u, \ldots, v_n = v$. Let $k$ be the least index with $v_k \notin S$. Then $k \ge 1$, $v_{k-1} \in S$, and the edge $s(v_{k-1}, v_k)$ crosses from $S$ to its complement.

Conversely, suppose every such $S$ has an edge across. Fix $u \in V$ and let $S$ be the set of vertices reachable from $u$. Then $u \in S$, so $S \neq \emptyset$. No edge goes from $S$ to its complement: if $a \in S$ and $a \sim b$, then $b$ is reachable from $u$ through $a$, so $b \in S$. By the hypothesis $S = V$. So every vertex is reachable from $u$, and by symmetry and transitivity any two vertices are reachable from each other. $\square$

The first half of the proof is `SimpleGraph.Walk.exists_boundary_dart`: a walk from a vertex in $S$ to a vertex outside $S$ has a dart from $S$ to the outside.

**Theorem (A graph or its complement is connected).** Let $V$ be nonempty. For each graph $G$ on $V$, at least one of $G$ and $\overline{G}$ is connected.

*Proof.* Suppose $G$ is not connected. Then $G$ has two vertices $u$ and $v$ in different components. Let $x$ and $y$ be any two vertices. If $x$ and $y$ lie in different components of $G$, then $x \not\sim_G y$, so $x \sim y$ in $\overline{G}$. If they lie in the same component $C$, choose a vertex $z \notin C$. This is possible since $u$ and $v$ are not both in $C$. Then $x$ and $z$ lie in different components, and so do $y$ and $z$, so $x \sim z \sim y$ in $\overline{G}$ when $x \neq y$. In both cases $y$ is reachable from $x$ in $\overline{G}$. $\square$

::: mathlib
`SimpleGraph.connected_or_connected_compl` · `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`

`G.Connected ∨ Gᶜ.Connected` for `[Nonempty V]`. The library proves it from `SimpleGraph.reachable_or_reachable_compl`, which says that for any three vertices `u`, `v`, `w`, either `v` is reachable from `u` in `G` or `w` is reachable from `u` in `Gᶜ`.

<?decl SimpleGraph.connected_or_connected_compl?>
:::

**Proposition (The distance is a metric).** Let $G$ be connected. Then $d(u, v)$ is finite, a shortest walk from $u$ to $v$ is a path, $d(u, v) = 0$ if and only if $u = v$, $d(u, v) = d(v, u)$, $d(u, v) = 1$ if and only if $u \sim v$, and $d(u, w) \le d(u, v) + d(v, w)$.

*Proof.* A walk from $u$ to $v$ exists, so the set of lengths is a nonempty set of natural numbers and has a least element. If a shortest walk repeated a vertex, the proof in Section 1 would give a shorter walk, so it is a path. A walk of length $0$ is empty, so it joins $u$ to itself only. A walk of length $1$ is one step, so $d(u, v) = 1$ exactly when $u \neq v$ and $u \sim v$, and $u \sim v$ implies $u \neq v$. Reversal is a bijection between the walks from $u$ to $v$ and from $v$ to $u$ that keeps the length, so $d$ is symmetric. For the triangle inequality, append a shortest walk from $u$ to $v$ and a shortest walk from $v$ to $w$. The result is a walk from $u$ to $w$ of length $d(u, v) + d(v, w)$. $\square$

**Proposition (Radius and diameter).** For a connected graph, $\operatorname{rad} G \le \operatorname{diam} G \le 2 \operatorname{rad} G$.

*Proof.* Each eccentricity lies between the infimum and the supremum of the eccentricities, so $\operatorname{rad} G \le e(u) \le \operatorname{diam} G$ for any vertex $u$, and $V$ is nonempty. For the second bound, the eccentricities are natural numbers or $\infty$, so the infimum is attained at a vertex $c$ with $e(c) = \operatorname{rad} G$. For any $u, v$,
$$d(u, v) \le d(u, c) + d(c, v) \le e(c) + e(c) = 2 \operatorname{rad} G.$$
Taking the supremum over $u$ and $v$ gives the bound. $\square$

### Examples

**Example (The Petersen graph has diameter 2).** Chapter 1, Section 1 found that two non-adjacent vertices of the Petersen graph $P$ have exactly one common neighbour. So for $u \neq v$, either $u \sim v$ and $d(u, v) = 1$, or $u \not\sim v$ and $u, w, v$ is a walk of length $2$ through the common neighbour $w$, so $d(u, v) = 2$. In particular $P$ is connected. The graph is not complete, since $\{1,2\} \not\sim \{1,3\}$, so the diameter is $2$. Each vertex has eccentricity $2$: it has $3$ neighbours at distance $1$ and $6$ vertices at distance $2$, as $1 + 3 + 6 = 10$. So the radius is $2$ and the center is the whole vertex set.

A count shows that $2$ is the least diameter possible for a 3-regular graph on $10$ vertices. A vertex $u$ of a 3-regular graph has at most $3$ vertices at distance $1$, and at most $3 \cdot 2 = 6$ at distance $2$, since each neighbour of $u$ has at most two neighbours other than $u$. So a 3-regular graph of diameter $2$ has at most $1 + 3 + 6 = 10$ vertices, and the Petersen graph meets this bound.

**Example (Paths and cycles).** Let $P_n$ be the path on the vertices $0, 1, \ldots, n-1$ with $i \sim i+1$. Then $d(i, j) = |i - j|$, since a walk changes the vertex by $1$ at each step. The eccentricity of $i$ is $\max(i, n - 1 - i)$, so $\operatorname{diam} P_n = n - 1$, attained at the two ends, and $\operatorname{rad} P_n = \lceil (n-1)/2 \rceil$, attained in the middle. For $n = 5$ the radius is $2$ and the diameter is $4 = 2 \operatorname{rad}$, so the bound of the proposition is sharp. In the cycle $C_n$ on $\mathbb{Z}/n$, $d(i, j)$ is the smaller of the two arcs, so each vertex has eccentricity $\lfloor n/2 \rfloor$ and $\operatorname{rad} C_n = \operatorname{diam} C_n = \lfloor n/2 \rfloor$.

**Counterexample (The diameter of a disconnected graph in Mathlib).** Let $G$ be the empty graph on two vertices $a$ and $b$. On paper $d(a, b) = \infty$ and the diameter is $\infty$. In Mathlib `G.edist a b = ⊤` and `G.ediam = ⊤`, but `G.dist a b = 0` and `G.diam = 0`, since `ENat.toNat ⊤ = 0`. A statement such as `G.dist u v ≤ G.diam` is therefore false without care: it holds when `G.ediam ≠ ⊤`, and this is the hypothesis of `SimpleGraph.dist_le_diam`.

### The library around it

The file `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected` has reachability, connectivity and components, with the setoid `SimpleGraph.reachableSetoid` and the equivalence `SimpleGraph.reachable_is_equivalence`. It also has `SimpleGraph.connected_top` and `SimpleGraph.connected_bot_iff`, and the equivalence of components under an isomorphism, `SimpleGraph.Iso.connectedComponentEquiv`. A component maps forward along a homomorphism by `SimpleGraph.ConnectedComponent.map`. Adding edges keeps preconnectivity, by `SimpleGraph.Preconnected.mono`. The metric is in `Mathlib.Combinatorics.SimpleGraph.Metric`, and the eccentricity, the radius, the diameter and the center are in `Mathlib.Combinatorics.SimpleGraph.Diam`, with `SimpleGraph.center_nonempty` on a nonempty type.

Common errors of a learner:

- `G.Reachable u v` is a proposition. In a proof of a goal that is a type, such as the construction of a walk, the walk cannot be extracted from it. Use `Classical.choice` on the `Nonempty` statement, and expect noncomputable definitions.
- `G.Connected` fails on the empty type. A lemma stated with `G.Connected` often has a form with `G.Preconnected` for the case of no vertices.
- `G.dist` and `G.diam` are natural numbers that hide the value $\infty$. Prefer `edist` and `ediam` in statements that must cover disconnected graphs.

### Exercises

1. (A) Show that $K_n$ is connected for $n \ge 1$ and that the empty graph on $n \ge 2$ vertices is not.
2. (A) Compute the components, the distances and the diameter of the graph on $\{1, \ldots, 6\}$ with edges $12, 23, 45$.
3. (A) Show that a connected graph on $n$ vertices has diameter at most $n - 1$.
4. (A) Compute the radius, the diameter and the center of the complete bipartite graph $K_{m,n}$ for $m, n \ge 2$.
5. (B) Show that a finite graph with $\delta(G) \ge (n-1)/2$ is connected and has diameter at most $2$. Hint: Exercise 7 of Chapter 1, Section 1.
6. (B) Show that if $G$ has diameter at least $3$, then $\overline{G}$ has diameter at most $3$.
7. (B) Show that each vertex $v$ of a finite graph satisfies $|C(v)| \ge \deg(v) + 1$, and deduce that a graph on $n$ vertices with $\delta(G) \ge n/2$ is connected.
8. (B) Let $G$ be connected and $e$ an edge on a cycle of $G$. Show that $G$ with $e$ deleted is connected.
9. (C) Let $G$ be $d$-regular with diameter $2$, $d \ge 2$. Show that $G$ has at most $d^2 + 1$ vertices, and that equality forces any two non-adjacent vertices to have exactly one common neighbour and adjacent vertices to have none.

### Notes and history

The metric of a connected graph is the path metric of the graph seen as a one-dimensional space with edges of length $1$. The bound of the Petersen example is the Moore bound for diameter $2$, and the graphs that meet it are the Moore graphs of Chapter 1, Section 2. The theorem that a graph or its complement is connected is a standard exercise in the books of Diestel and Bollobás. The header of `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected` lists Kyle Miller. The header of `Mathlib.Combinatorics.SimpleGraph.Metric` lists Vincent Beffara, Rida Hamadani and Nelson Spence with Kyle Miller, and the header of `Mathlib.Combinatorics.SimpleGraph.Diam` lists Rida Hamadani.

### Reference

<?reference?>
