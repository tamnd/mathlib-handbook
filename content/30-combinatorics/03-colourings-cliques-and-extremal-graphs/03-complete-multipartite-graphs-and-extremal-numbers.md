---
title: Complete multipartite graphs and extremal numbers
kind: api
modules:
  - Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
  - Mathlib.Combinatorics.SimpleGraph.FiveWheelLike
  - Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
  - Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz
  - Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits
explains:
  E2: [SimpleGraph.not_isCompleteMultipartite_iff_exists_isPathGraph3Compl, SimpleGraph.IsCompleteMultipartite.colorable_of_cliqueFree, SimpleGraph.card_edgeFinset_completeEquipartiteGraph, SimpleGraph.colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree, SimpleGraph.antitoneOn_extremalNumber_div_choose_two, SimpleGraph.zarankiewicz_le_extremalNumber, SimpleGraph.two_mul_extremalNumber_le_zarankiewicz_symm]
  E1: auto
families: []
requires: [V30.C01, V30.C02, V03.C03, V03.C06, V15]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Complete multipartite graphs and extremal numbers

### Overview

Section 2 proves the theorem of Turán: among the graphs on $n$ vertices with no clique of size $r + 1$, the Turán graph $T(n, r)$ has the most edges. The Turán graph is complete multipartite. Its vertices fall into $r$ classes, and two vertices are adjacent exactly when they lie in different classes. This section studies the complete multipartite graphs in general and then the extremal numbers $\operatorname{ex}(n, H)$ of Section 2 for a forbidden graph $H$ that is not a clique.

The first two modules give a characterization. A graph is complete multipartite when non-adjacency is transitive. A maximal graph with no $K_{r+1}$ is $r$-colourable if and only if it is complete multipartite, and the proof uses a small configuration called a five-wheel-like structure. The same structure gives the theorem of Andrásfai, Erdős and Sós on triangle-free graphs of large minimum degree. The last three modules are about asymptotics. The Turán density $\pi(H)$ is the limit of $\operatorname{ex}(n, H) / \binom{n}{2}$. The Zarankiewicz function counts the edges of bipartite graphs with no complete bipartite subgraph. The Erdős-Stone theorem, in its form for the minimum degree, finds a complete multipartite graph with large parts inside a dense graph.

The section needs Sections 1 and 2 of this chapter, the copies and the containment relation $H \sqsubseteq G$ of Chapter 1, Section 2, and limits of real sequences from Volume 15.

### The library around it

#### Complete multipartite graphs

The module `Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite` defines `G.IsCompleteMultipartite` as the transitivity of the relation $x \not\sim y$. Non-adjacency is always reflexive and symmetric, so for such a graph it is an equivalence relation, `SimpleGraph.IsCompleteMultipartite.setoid`. Its classes are the parts. Inside a part there is no edge, and between two parts every edge is present. The isomorphism `SimpleGraph.IsCompleteMultipartite.iso` sends $G$ to `SimpleGraph.completeMultipartiteGraph` of the family of its parts, and `SimpleGraph.isCompleteMultipartite_iff` is the statement that $G$ is complete multipartite if and only if it is isomorphic to `completeMultipartiteGraph V` for a family of nonempty types `V i`. The complete graph, the empty graph, the complete bipartite graphs and the star graphs of Chapter 1, Section 3 are complete multipartite (`SimpleGraph.IsCompleteMultipartite.top`, `SimpleGraph.IsCompleteMultipartite.bot`, `SimpleGraph.IsCompleteMultipartite.completeBipartiteGraph`). The property passes to induced subgraphs (`SimpleGraph.IsCompleteMultipartite.induce`) and along embeddings (`SimpleGraph.IsCompleteMultipartite.comap`).

The failure of transitivity has a witness. The predicate `G.IsPathGraph3Compl v w₁ w₂` says that $w_1 \sim w_2$, $v \not\sim w_1$ and $v \not\sim w_2$. The three vertices induce one edge and one isolated vertex, which is the complement of the path $P_3$. Hence the name.

**Theorem.** A graph is not complete multipartite if and only if it has vertices $v, w_1, w_2$ with `G.IsPathGraph3Compl v w₁ w₂`.

*Proof.* If $w_1 \sim w_2$, $v \not\sim w_1$ and $v \not\sim w_2$, then $w_1 \not\sim v$ and $v \not\sim w_2$ but $w_1 \sim w_2$, so non-adjacency is not transitive. Conversely, if transitivity fails, there are $x \not\sim y$ and $y \not\sim z$ with $x \sim z$. Then $v = y$, $w_1 = x$ and $w_2 = z$ is a witness. $\square$

This is `SimpleGraph.not_isCompleteMultipartite_iff_exists_isPathGraph3Compl`. The witness gives an embedding of the graph $\overline{P_3}$ into $G$ (`SimpleGraph.IsPathGraph3Compl.pathGraph3ComplEmbedding`), so a graph is complete multipartite if and only if it has no induced $\overline{P_3}$ (`SimpleGraph.not_isCompleteMultipartite_of_pathGraph3ComplEmbedding`).

**Theorem.** A complete multipartite graph with no clique of size $n$ is $(n - 1)$-colourable.

*Proof.* Choose one vertex in each part. Two chosen vertices lie in different parts, so they are adjacent, and the chosen set is a clique. So there are at most $n - 1$ parts. Colour each vertex by its part. Two vertices of the same colour lie in one part and are not adjacent. $\square$

This is `SimpleGraph.IsCompleteMultipartite.colorable_of_cliqueFree`.

The module also defines the complete equipartite graph `SimpleGraph.completeEquipartiteGraph r t`, written $K_r(t)$, with $r$ parts of size $t$. Its vertex type is the product `Fin r × Fin t`, and $v \sim w$ if and only if $v_1 \neq w_1$ (`SimpleGraph.completeEquipartiteGraph_adj`). The library uses a product type here and not the dependent sum type of `completeMultipartiteGraph`. The isomorphisms `SimpleGraph.completeEquipartiteGraph.completeMultipartiteGraph` and `SimpleGraph.completeEquipartiteGraph.turanGraph` connect the two forms and identify $K_r(t)$ with the Turán graph $T(rt, r)$. Each vertex has degree $(r - 1)t$ (`SimpleGraph.degree_completeEquipartiteGraph`).

**Theorem.** $K_r(t)$ has $\binom{r}{2} t^2$ edges.

*Proof.* An edge joins two different parts. There are $\binom{r}{2}$ pairs of parts, and two parts of size $t$ are joined by $t^2$ edges. $\square$

This is `SimpleGraph.card_edgeFinset_completeEquipartiteGraph`. The degree-sum formula of Section 1 gives the same count: $rt \cdot (r - 1)t / 2 = \binom{r}{2} t^2$.

A copy of $K_r(t)$ inside a graph $G$ is the structure `G.CompleteEquipartiteSubgraph r t`. It holds a finset `parts` of $r$ disjoint finsets of size $t$, with all edges of $G$ between two different members (`SimpleGraph.CompleteEquipartiteSubgraph.isCompleteBetween`). The vertex set has $rt$ elements (`SimpleGraph.CompleteEquipartiteSubgraph.card_verts`). The structure is equivalent to a copy, by `SimpleGraph.CompleteEquipartiteSubgraph.toCopy` and `SimpleGraph.CompleteEquipartiteSubgraph.ofCopy`, and `SimpleGraph.completeEquipartiteGraph_isContained_iff` is the statement for containment. In the other direction, `SimpleGraph.isContained_completeEquipartiteGraph_of_colorable` says that a graph with an $n$-colouring whose colour classes have at most $t$ vertices is contained in $K_n(t)$. So every graph $H$ with $\chi(H) = r + 1$ is contained in $K_{r+1}(t)$ for $t = |V(H)|$.

#### Maximal clique-free graphs and five-wheel-like structures

A graph $G$ is maximal with no $K_{r+1}$ when it has no $K_{r+1}$, but each added edge creates one. In Mathlib this is `Maximal (fun H => H.CliqueFree (r + 1)) G`, with the predicate `Maximal` of Volume 4. The Turán graph is such a graph. The module `Mathlib.Combinatorics.SimpleGraph.FiveWheelLike` proves that the maximal graphs that are $r$-colourable are exactly the complete multipartite ones.

The tool is the predicate `G.IsFiveWheelLike r k v w₁ w₂ s t`. Here $v, w_1, w_2$ form an `IsPathGraph3Compl`, the sets $s$ and $t$ have $r$ elements and avoid these three vertices, the four sets $s \cup \{v\}$, $s \cup \{w_1\}$, $t \cup \{v\}$ and $t \cup \{w_2\}$ are cliques of size $r + 1$, and $|s \cap t| = k$. The field lemmas are `SimpleGraph.IsFiveWheelLike.isNClique_left`, `SimpleGraph.IsFiveWheelLike.isNClique_fst_left`, `SimpleGraph.IsFiveWheelLike.card_inter` and their companions. For $r = 1$ and $k = 0$ the structure is a five-cycle $v, s, w_1, w_2, t$. For $r = 2$ and $k = 1$ it is a five-cycle with one more vertex joined to all five, a wheel with five spokes. The predicate `G.FiveWheelLikeFree r k` says that no such structure exists.

**Theorem.** Let $G$ be maximal with no $K_{r+1}$. Then $G$ is $r$-colourable if and only if $G$ is complete multipartite.

*Proof sketch.* If $G$ is complete multipartite, the previous theorem with $n = r + 1$ gives an $r$-colouring. Conversely, assume that $G$ is not complete multipartite, and write $r = r' + 1$. Take a witness $v, w_1, w_2$. The pairs $v w_1$ and $v w_2$ are not edges, so by maximality the addition of each of them creates a clique of size $r' + 2$. Remove the new edge from these cliques. This gives $r'$-sets $s$ and $t$ such that $s \cup \{v\}$, $s \cup \{w_1\}$, $t \cup \{v\}$ and $t \cup \{w_2\}$ are cliques of size $r' + 1$. This is a five-wheel-like structure (`SimpleGraph.exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`). Such a structure is not $(r' + 1)$-colourable (`SimpleGraph.IsFiveWheelLike.not_colorable_succ`). In a colouring with $r' + 1$ colours, the clique $s \cup \{v\}$ uses all colours, so $v$ and $w_1$ get the one colour that $s$ misses, and in the same way $v$ and $w_2$ get the one colour that $t$ misses. A comparison of the colours on $s \cap t$ and on $s \setminus t$, $t \setminus s$ forces $w_1$ and $w_2$ to have the same colour. But $w_1 \sim w_2$. $\square$

This is `SimpleGraph.colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree`. The same structures give a bound on the minimum degree. If $G$ has no $K_{r+2}$, contains a structure $W_{r,k}$ and has no structure $W_{r,k+1}$, then $\delta(G) \le (2r + k)n / (2r + k + 3)$ (`SimpleGraph.IsFiveWheelLike.minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ`). From this the module derives the theorem of Andrásfai, Erdős and Sós.

**Theorem (Andrásfai, Erdős and Sós).** Let $G$ be a graph on $n$ vertices with no $K_{r+1}$ and with $\delta(G) > \frac{3r - 4}{3r - 1} n$. Then $G$ is $r$-colourable.

This is `SimpleGraph.colorable_of_cliqueFree_lt_minDegree`, and the text states it without proof. The quotient in the hypothesis is the division of `ℕ`. For $r = 2$ it says that a triangle-free graph with minimum degree more than $2n/5$ is bipartite. The blow-ups of the five-cycle show that the constant $2/5$ cannot be lowered.

#### The Turán density

The module `Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity` defines the Turán density `H.turanDensity` as the limit of the real numbers $\operatorname{ex}(n, H) / \binom{n}{2}$, with `limUnder` of the filter `atTop`. The limit exists because the sequence decreases.

**Theorem.** For every graph $H$, the sequence $\operatorname{ex}(n, H) / \binom{n}{2}$ is non-increasing for $n \geq 2$.

*Proof.* Let $G$ be an $H$-free graph on $n + 1$ vertices with $\operatorname{ex}(n + 1, H)$ edges. For each vertex $u$, the graph $G - u$ is $H$-free on $n$ vertices, so it has at most $\operatorname{ex}(n, H)$ edges. Each edge of $G$ survives in $G - u$ for exactly $n - 1$ choices of $u$. Sum over $u$: $(n - 1)\operatorname{ex}(n + 1, H) \leq (n + 1)\operatorname{ex}(n, H)$. Divide by $(n - 1)(n + 1) n / 2$, and use $\binom{n+1}{2} = (n + 1)n/2$ and $\binom{n}{2} = n(n - 1)/2$. $\square$

This is `SimpleGraph.antitoneOn_extremalNumber_div_choose_two`, with the set `Set.Ici 2`. The sequence lies in $[0, 1]$, so it converges to its infimum. The library states this as `SimpleGraph.tendsto_turanDensity`, `SimpleGraph.isGLB_turanDensity` and `SimpleGraph.turanDensity_eq_csInf`, with the bounds `SimpleGraph.turanDensity_nonneg`, `SimpleGraph.turanDensity_le_one` and `SimpleGraph.turanDensity_le_extremalNumber_div_choose_two`. When $\pi(H) \neq 0$, the extremal number is asymptotic to $\pi(H) \binom{n}{2}$ (`SimpleGraph.isEquivalent_extremalNumber`, with `Asymptotics.IsEquivalent`).

The density is a threshold for containment. For each $\varepsilon > 0$ and all large $n$, a graph on $n$ vertices with at least $(\pi(H) + \varepsilon)\binom{n}{2}$ edges contains $H$ (`SimpleGraph.eventually_isContained_of_card_edgeFinset`, stated for graphs on `Fin n`). The form `SimpleGraph.isContained_of_card_edgeFinset` holds for any finite vertex type with at least `H.turanDensityConst ε` elements, and `SimpleGraph.card_le_turanDensityConst` bounds this constant from below by $|V(H)|$.

#### The Zarankiewicz function

The module `Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz` defines `SimpleGraph.zarankiewicz m n s t`, written $z(m, n; s, t)$. It is the largest number of edges of a subgraph of $K_{m,n}$ on `Fin m ⊕ Fin n` that does not contain $K_{s,t}$. The containment uses `SimpleGraph.Free` of Chapter 1, so a copy of $K_{s,t}$ may put its part of size $s$ on either side. The lemma `SimpleGraph.zarankiewicz_of_fintypeCard_eq` moves the definition to any finite types with the right cards, and `SimpleGraph.zarankiewicz_le_iff` and `SimpleGraph.lt_zarankiewicz_iff` are the order forms that a proof of a bound uses.

**Theorem.** $z(m, n; s, t) \leq \operatorname{ex}(m + n, K_{s,t})$, and $2 \operatorname{ex}(n, K_{s,t}) \leq z(n, n; s, t)$ when $t \geq 1$.

*Proof.* A subgraph of $K_{m,n}$ with no $K_{s,t}$ is a $K_{s,t}$-free graph on $m + n$ vertices. This gives the first bound. For the second, let $G$ be $K_{s,t}$-free on $n$ vertices. Its bipartite double cover $B$ has two copies $V_1, V_2$ of the vertices, with $x_1 \sim y_2$ when $x \sim y$ in $G$. So $B$ has $2|E(G)|$ edges. A copy of $K_{s,t}$ in $B$ is connected, so it has one part in $V_1$ and the other part in $V_2$. These parts are disjoint as sets of vertices of $G$, because $G$ has no loop, and every vertex of one part is adjacent in $G$ to every vertex of the other. So $G$ contains $K_{s,t}$, a contradiction. $\square$

These are `SimpleGraph.zarankiewicz_le_extremalNumber` and `SimpleGraph.two_mul_extremalNumber_le_zarankiewicz_symm`. In the Lean statement the hypothesis on $t$ is `Nonempty β`.

#### The Erdős-Stone theorem

The module `Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits` holds one public theorem, the form of the Erdős-Stone theorem for the minimum degree.

**Theorem (Erdős and Stone).** Let $\varepsilon > 0$ and $r, t \in \mathbb{N}$. For all large $n$, a graph $G$ on $n$ vertices with $\delta(G) \geq (1 - 1/r + \varepsilon)n$ contains $K_{r+1}(t)$.

This is `SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree`, stated for graphs on `Fin n`, and the text states it without proof. The bound is sharp in the leading term: the Turán graph $T(n, r)$ has minimum degree about $(1 - 1/r)n$ and no $K_{r+1}$. With `SimpleGraph.isContained_completeEquipartiteGraph_of_colorable`, the theorem applies to every graph $H$ with $\chi(H) = r + 1$, because $H$ is contained in $K_{r+1}(t)$ for $t = |V(H)|$.

#### Common errors

1. A learner proves `G.IsCompleteMultipartite` by exhibiting a partition into independent sets. That is a colouring, not the definition. The definition needs every edge between two different classes, and the direct route is the transitivity of non-adjacency.
2. A learner uses `SimpleGraph.colorable_of_cliqueFree_lt_minDegree` with the real bound $\frac{3r - 4}{3r - 1}n$. The hypothesis is the natural number `(3 * r - 4) * ‖α‖ / (3 * r - 1)`, with division in `ℕ` and the truncated subtraction for small $r$. For $r \le 1$ the expression is $0$.
3. A learner reads `SimpleGraph.zarankiewicz m n s t` with an ordered $K_{s,t}$, with the part of size $s$ on the side of size $m$. The definition forbids every copy of $K_{s,t}$, also the copies with the parts swapped.

### Exercises

1. (A) Show that the five-cycle is not complete multipartite. Give an explicit witness `G.IsPathGraph3Compl v w₁ w₂`.
2. (A) Show that $K_r(t)$ has no clique of size $r + 1$ and that it is $r$-colourable. Compute its number of edges for $r = 3$ and $t = 2$.
3. (B) Show that $\pi(K_3) \le 1/2$ from Mantel's theorem of Section 2 and the definition of the Turán density as a limit.
4. (B) Show that a complete multipartite graph is maximal with no $K_{r+1}$ if and only if it has exactly $r$ nonempty parts.
5. (B) Show that $z(m, n; 1, 1) = 0$ and that $z(n, n; 1, 2) = n$.
6. (C) Prove the case $r = 2$ of the theorem of Andrásfai, Erdős and Sós: a triangle-free graph on $n$ vertices with $\delta(G) > 2n/5$ has no odd cycle. Hint: take a shortest odd cycle, show that it has length $5$ when it is not a triangle and the bound fails otherwise, and count the edges from the cycle to the rest.

### Reference

<?reference?>
