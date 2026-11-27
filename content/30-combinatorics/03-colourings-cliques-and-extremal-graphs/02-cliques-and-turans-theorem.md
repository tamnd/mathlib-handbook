---
title: Cliques and Turán's theorem
kind: theory
modules:
  - Mathlib.Combinatorics.SimpleGraph.Clique
  - Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
  - Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
explains:
  E3: [SimpleGraph.IsClique, SimpleGraph.IsNClique, SimpleGraph.CliqueFree, SimpleGraph.IsIndepSet, SimpleGraph.IsTuranMaximal, SimpleGraph.turanGraph, SimpleGraph.turanGraph_cliqueFree, SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph, SimpleGraph.CliqueFree.card_edgeFinset_le, SimpleGraph.turanNumber_two, SimpleGraph.extremalNumber]
  E2: [SimpleGraph.isClique_iff, SimpleGraph.isNClique_iff, SimpleGraph.is3Clique_triple_iff, SimpleGraph.isClique_pair, SimpleGraph.IsClique.subset, SimpleGraph.CliqueFree.mono, SimpleGraph.CliqueFree.anti, SimpleGraph.cliqueFree_of_card_lt, SimpleGraph.cliqueFree_two, SimpleGraph.cliqueFree_bot, SimpleGraph.not_cliqueFree_iff_top_isContained, SimpleGraph.cliqueFinset, SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.cliqueFinset_eq_empty_iff, SimpleGraph.card_cliqueFinset_le, SimpleGraph.cliqueNum, SimpleGraph.IsClique.card_le_cliqueNum, SimpleGraph.isClique_compl, SimpleGraph.isIndepSet_compl, SimpleGraph.isIndepSet_neighborSet_of_triangleFree, SimpleGraph.IsNIndepSet, SimpleGraph.IsExtremal, SimpleGraph.exists_isExtremal_iff_exists, SimpleGraph.card_edgeFinset_le_extremalNumber, SimpleGraph.IsContained.of_extremalNumber_lt_card_edgeFinset, SimpleGraph.extremalNumber_le_iff, SimpleGraph.extremalNumber_le_choose_two, SimpleGraph.turanGraph_adj, SimpleGraph.turanGraph_eq_top, SimpleGraph.exists_isTuranMaximal, SimpleGraph.IsTuranMaximal.degree_eq_of_not_adj, SimpleGraph.IsTuranMaximal.not_adj_trans, SimpleGraph.IsTuranMaximal.equivalence_not_adj, SimpleGraph.IsTuranMaximal.finpartition, SimpleGraph.IsTuranMaximal.isEquipartition, SimpleGraph.IsTuranMaximal.card_parts, SimpleGraph.isTuranMaximal_turanGraph, SimpleGraph.extremalNumber_top, SimpleGraph.turanNumber, SimpleGraph.turanNumber_eq, SimpleGraph.turanNumber_three, SimpleGraph.mul_turanNumber_le]
  E1: auto
families: []
requires: [V30.C01, V30.C02, V03.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cliques and Turán's theorem

### Overview

A clique is a set of vertices that are pairwise adjacent. A graph with many edges must contain large cliques, and the question of this section is exactly how many edges force a clique of a given size. For triangles, the answer is the theorem of Mantel from 1907: a graph on $n$ vertices with more than $n^2/4$ edges contains a triangle. Turán found the answer for all clique sizes in 1941. A graph on $n$ vertices without a clique of size $r + 1$ has at most as many edges as the complete $r$-partite graph with parts as equal as possible, and this graph is the only one that attains the bound.

The theorem of Turán is the start of extremal graph theory. For a fixed graph $H$, the extremal number $\operatorname{ex}(n, H)$ is the largest number of edges of a graph on $n$ vertices that does not contain $H$. Turán computes it when $H$ is a complete graph. Mathlib has the extremal numbers for an arbitrary $H$, the Turán graphs, and a full proof of the theorem of Turán with its uniqueness part.

This section defines cliques, clique-free graphs and independent sets. It proves Mantel by double counting, and then proves Turán by the symmetrisation of Zykov, which is also the proof in Mathlib. It computes the number of edges of the Turán graph.

### Definitions

**Definition (Clique).** Let $G$ be a graph on $V$. A set $s \subseteq V$ is a clique when any two distinct vertices of $s$ are adjacent. An $n$-clique is a finite clique with exactly $n$ elements. A $3$-clique is a triangle.

**Definition (Clique-free).** The graph $G$ is $n$-clique-free when it has no $n$-clique. The clique number $\omega(G)$ is the largest $n$ such that $G$ has an $n$-clique.

**Definition (Independent set).** A set $s \subseteq V$ is independent when no two vertices of $s$ are adjacent. A set is independent in $G$ if and only if it is a clique in the complement $\overline{G}$.

::: mathlib
`SimpleGraph.IsClique` · `Mathlib.Combinatorics.SimpleGraph.Clique`

`G.IsClique s` is an abbreviation for `s.Pairwise G.Adj`, for a set `s : Set α`. The unfolding is `SimpleGraph.isClique_iff`. A subset of a clique is a clique, `SimpleGraph.IsClique.subset`, and a pair is a clique if and only if its two points are adjacent or equal, `SimpleGraph.isClique_pair`. The clique number `SimpleGraph.cliqueNum` is a natural number, and each finite clique has at most that size, `SimpleGraph.IsClique.card_le_cliqueNum`.

<?decl SimpleGraph.IsClique?>
:::

::: mathlib
`SimpleGraph.IsNClique` · `Mathlib.Combinatorics.SimpleGraph.Clique`

`G.IsNClique n s` is a structure on a finset `s`, with the two fields "clique" and "cardinality". The interface is `SimpleGraph.isNClique_iff`, `G.IsNClique n s ↔ G.IsClique s ∧ #s = n`. For triangles, `SimpleGraph.is3Clique_triple_iff` gives `G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c`. On a finite type, `G.cliqueFinset n` is the finset of all $n$-cliques, with `SimpleGraph.mem_cliqueFinset_iff` and the bound `SimpleGraph.card_cliqueFinset_le` by $\binom{|V|}{n}$.

<?decl SimpleGraph.IsNClique?>
:::

::: mathlib
`SimpleGraph.CliqueFree` · `Mathlib.Combinatorics.SimpleGraph.Clique`

`G.CliqueFree n` is `∀ t, ¬G.IsNClique n t`. It is monotone in $n$, `SimpleGraph.CliqueFree.mono`, and antitone in the graph, `SimpleGraph.CliqueFree.anti`. A graph on fewer than $n$ vertices is $n$-clique-free, `SimpleGraph.cliqueFree_of_card_lt`, and a graph is $2$-clique-free if and only if it has no edge, `SimpleGraph.cliqueFree_two`. The link to subgraph containment is `SimpleGraph.not_cliqueFree_iff_top_isContained`: $G$ has an $n$-clique if and only if it contains a copy of `completeGraph (Fin n)`. On a finite type, `SimpleGraph.cliqueFinset_eq_empty_iff` says that `G.CliqueFree n` holds exactly when `G.cliqueFinset n` is empty.

<?decl SimpleGraph.CliqueFree?>
:::

::: mathlib
`SimpleGraph.IsIndepSet` · `Mathlib.Combinatorics.SimpleGraph.Clique`

`G.IsIndepSet s` is `s.Pairwise (fun v w ↦ ¬G.Adj v w)`. The two links with the complement are `SimpleGraph.isClique_compl` and `SimpleGraph.isIndepSet_compl`, both simp lemmas. The finset version with a size is the structure `SimpleGraph.IsNIndepSet`. In a triangle-free graph, each neighbourhood is independent, `SimpleGraph.isIndepSet_neighborSet_of_triangleFree`. This fact is the start of the proof of Mantel below.

<?decl SimpleGraph.IsIndepSet?>
:::

**Definition (Extremal number).** Let $H$ be a graph. A graph $G$ is $H$-free when it contains no copy of $H$, that is, no injective homomorphism from $H$ to $G$. The extremal number $\operatorname{ex}(n, H)$ is the largest number of edges of an $H$-free graph on $n$ vertices.

The maximum exists because there are finitely many graphs on $n$ vertices, and the empty graph is $H$-free when $H$ has an edge.

::: mathlib
`SimpleGraph.extremalNumber` · `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic`

`extremalNumber n H` is the supremum of `#G.edgeFinset` over the $H$-free graphs `G` on `Fin n`. The interface does not use `Fin n` directly. `SimpleGraph.card_edgeFinset_le_extremalNumber` says that an $H$-free graph on a finite type `V` has at most `extremalNumber (card V) H` edges, and `SimpleGraph.IsContained.of_extremalNumber_lt_card_edgeFinset` is the contrapositive. `SimpleGraph.extremalNumber_le_iff` turns an upper bound for the extremal number into a statement about all $H$-free graphs on `V`. The trivial bound is `SimpleGraph.extremalNumber_le_choose_two`. The predicate `G.IsExtremal p` says that `G` satisfies `p` and has the most edges among the graphs on the same type that satisfy `p`. `SimpleGraph.exists_isExtremal_iff_exists` gives an extremal graph as soon as one graph satisfies `p`.

<?decl SimpleGraph.extremalNumber?>
:::

**Definition (Turán graph).** Let $n$ and $r \ge 1$ be natural numbers. The Turán graph $T(n, r)$ has the vertex set $\{0, 1, \dots, n - 1\}$, and $v \sim w$ if and only if $v \not\equiv w \pmod r$. Its vertices fall into $r$ classes by the residue mod $r$. Each class is independent, two vertices in different classes are adjacent, and the sizes of two classes differ by at most $1$. The number of edges of $T(n, r)$ is the Turán number $t(n, r)$.

**Definition (Turán-maximal).** A finite graph $G$ is Turán-maximal for $r$ when it is $(r+1)$-clique-free and no $(r+1)$-clique-free graph on the same vertex set has more edges.

::: mathlib
`SimpleGraph.turanGraph` · `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`

`turanGraph n r : SimpleGraph (Fin n)` has `Adj v w := v % r ≠ w % r`, with the unfolding `SimpleGraph.turanGraph_adj`. For `r = 0` the residue is the vertex itself, so the graph is complete. More generally, `SimpleGraph.turanGraph_eq_top` gives `turanGraph n r = ⊤ ↔ r = 0 ∨ n ≤ r`. `SimpleGraph.turanNumber n r` is the abbreviation `#(turanGraph n r).edgeFinset`.

<?decl SimpleGraph.turanGraph?>
:::

::: mathlib
`SimpleGraph.IsTuranMaximal` · `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`

`G.IsTuranMaximal r` is defined as `G.IsExtremal (CliqueFree · (r + 1))`. A Turán-maximal graph exists on each finite type when `0 < r`, `SimpleGraph.exists_isTuranMaximal`. The steps of the proof below have the names `SimpleGraph.IsTuranMaximal.degree_eq_of_not_adj`, `SimpleGraph.IsTuranMaximal.not_adj_trans`, `SimpleGraph.IsTuranMaximal.equivalence_not_adj`, `SimpleGraph.IsTuranMaximal.finpartition`, `SimpleGraph.IsTuranMaximal.isEquipartition` and `SimpleGraph.IsTuranMaximal.card_parts`.

<?decl SimpleGraph.IsTuranMaximal?>
:::

### Theorems and proofs

**Theorem (Mantel).** Let $G$ be a triangle-free graph on $n$ vertices with $m$ edges. Then $m \le n^2/4$.

*Proof.* Let $uv$ be an edge. The neighbourhoods $N(u)$ and $N(v)$ are disjoint, because a common neighbour $w$ gives the triangle $uvw$. Thus $d(u) + d(v) \le n$. Add this inequality over all $m$ edges:
$$\sum_{uv \in E} \big(d(u) + d(v)\big) \le nm.$$
On the left, each vertex $w$ occurs once for each edge at $w$, that is, $d(w)$ times. Thus the left side is $\sum_{w} d(w)^2$. By the Cauchy-Schwarz inequality and the handshake lemma of Chapter 1,
$$\sum_w d(w)^2 \ge \frac{1}{n}\Big(\sum_w d(w)\Big)^2 = \frac{(2m)^2}{n}.$$
Thus $4m^2/n \le nm$. If $m = 0$ the claim is clear. Otherwise divide by $m$ to get $m \le n^2/4$. $\square$

The bound is sharp. The complete bipartite graph $K_{\lfloor n/2 \rfloor, \lceil n/2 \rceil}$ is bipartite, so it has no odd cycle and no triangle, and it has $\lfloor n/2 \rfloor \lceil n/2 \rceil = \lfloor n^2/4 \rfloor$ edges.

**Proposition.** For $r \ge 1$, the Turán graph $T(n, r)$ has no $(r+1)$-clique.

*Proof.* A clique has at most one vertex in each residue class, because two vertices in the same class are not adjacent. There are $r$ classes. $\square$

::: mathlib
`SimpleGraph.turanGraph_cliqueFree` · `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`

`turanGraph_cliqueFree (hr : 0 < r) : (turanGraph n r).CliqueFree (r + 1)`. The hypothesis `0 < r` is necessary: `turanGraph n 0` is complete.

<?decl SimpleGraph.turanGraph_cliqueFree?>
:::

**Theorem (Turán).** Let $r \ge 1$ and let $G$ be a graph on a finite set $V$ with $|V| = n$. Then $G$ is Turán-maximal for $r$ if and only if $G$ is isomorphic to $T(n, r)$. In particular, an $(r+1)$-clique-free graph on $n$ vertices has at most $t(n, r)$ edges.

*Proof.* Two edits of a graph are used. For vertices $s \ne t$, to replace $t$ by a copy of $s$ is to delete all edges at $t$ and then join $t$ to each vertex of $N(s)$. The new graph is $G'$. If $s \not\sim t$ in $G$, then $s \notin N(s)$ and $t \notin N(s)$, so the new edges at $t$ go to $N(s)$ and $t$ has degree $d(s)$ in $G'$.

*Step 1. The edit keeps the clique-free condition.* Suppose $G$ has no $(r+1)$-clique and $s \not\sim t$. Let $K$ be a clique in $G'$. If $t \notin K$, then $K$ is a clique in $G$, because the edges of $G'$ that do not touch $t$ are edges of $G$. If $t \in K$, then $s \notin K$ because $s$ and $t$ are not adjacent in $G'$. The set $(K \setminus \{t\}) \cup \{s\}$ is then a clique in $G$ of the same size: the vertices of $K \setminus \{t\}$ are neighbours of $t$ in $G'$, so they are in $N(s)$. Thus $G'$ has no $(r+1)$-clique.

*Step 2. Non-adjacent vertices have the same degree.* Let $G$ be Turán-maximal and $s \not\sim t$. Suppose $d(s) > d(t)$. Replace $t$ by a copy of $s$. The edit deletes $d(t)$ edges and adds $d(s)$ edges, so $G'$ has more edges than $G$, and $G'$ is $(r+1)$-clique-free by Step 1. This contradicts the maximality. By symmetry $d(s) = d(t)$.

*Step 3. Non-adjacency is transitive.* Let $G$ be Turán-maximal, and let $t \not\sim s$ and $s \not\sim u$ with $t \ne u$. Suppose $t \sim u$. By Step 2, $d(t) = d(s) = d(u)$. Replace $t$ by a copy of $s$, and then $u$ by a copy of $s$. The two deletions remove $d(t) + d(u) - 1$ edges, because the edge $tu$ is counted twice. The two joins add $2 d(s)$ edges, because $s$ is adjacent to neither $t$ nor $u$, so the neighbourhood of $s$ does not change. The net gain is $2d(s) - (2d(s) - 1) = 1$. By Step 1, applied twice, the result is $(r+1)$-clique-free. This contradicts the maximality.

*Step 4. $G$ is complete multipartite.* The relation "$v = w$ or $v \not\sim w$" is reflexive and symmetric, and it is transitive by Step 3. Its classes $P_1, \dots, P_k$ partition $V$. Each class is independent, and two vertices in different classes are adjacent. Choose one vertex in each class. These vertices form a $k$-clique, so $k \le r$.

*Step 5. The parts are as equal as possible.* Suppose $|P_i| \ge |P_j| + 2$. Move one vertex $v$ from $P_i$ to $P_j$ and form the complete multipartite graph on the new parts. The vertex $v$ loses the $|P_j|$ edges to $P_j$ and gains $|P_i| - 1$ edges to the rest of $P_i$. All other edges stay. The gain is $|P_i| - 1 - |P_j| \ge 1$, and the new graph has $k$ parts, so it is $(r+1)$-clique-free. This contradicts the maximality.

*Step 6. There are $\min(n, r)$ parts.* Suppose $k < r$ and $k < n$. Then some part has at least two vertices. Split it into two non-empty parts. This adds at least one edge and gives $k + 1 \le r$ parts, which contradicts the maximality.

Thus $G$ is complete multipartite with $\min(n, r)$ parts whose sizes differ by at most $1$. The graph $T(n, r)$ has the same description. Two complete multipartite graphs with the same multiset of part sizes are isomorphic, so $G \cong T(n, r)$.

For the converse, a Turán-maximal graph on $V$ exists, because there are finitely many graphs on $V$ and the empty graph is $(r+1)$-clique-free. By the first part it is isomorphic to $T(n, r)$. An isomorphism keeps the number of edges and the clique-free condition, so each graph isomorphic to $T(n, r)$ is also Turán-maximal. The last claim follows: an $(r+1)$-clique-free graph has at most as many edges as a Turán-maximal graph on the same set, that is, $t(n, r)$. $\square$

::: mathlib
`SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph` · `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`

`isTuranMaximal_iff_nonempty_iso_turanGraph (hr : 0 < r) : G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph (card V) r)`. The forward direction is the symmetrisation above. Mathlib does not build the parts by hand. It proves `SimpleGraph.IsTuranMaximal.equivalence_not_adj`, makes a setoid from it, and takes `SimpleGraph.IsTuranMaximal.finpartition`, the `Finpartition` of `univ` into the classes. `SimpleGraph.IsTuranMaximal.isEquipartition` is Step 5 and `SimpleGraph.IsTuranMaximal.card_parts` is Step 6. The reverse direction uses `SimpleGraph.isTuranMaximal_turanGraph`.

<?decl SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph?>
:::

::: mathlib
`SimpleGraph.CliqueFree.card_edgeFinset_le` · `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`

`CliqueFree.card_edgeFinset_le (cf : G.CliqueFree (r + 1)) : #G.edgeFinset ≤ turanNumber (Fintype.card V) r`. This is the edge bound in the form that a user needs most often. It has no hypothesis on `r`: for `r = 0` the graph is $1$-clique-free, so it has no vertex. In the language of extremal numbers, `SimpleGraph.extremalNumber_top` gives `extremalNumber n (⊤ : SimpleGraph α) = #(turanGraph n (card α - 1)).edgeFinset`.

<?decl SimpleGraph.CliqueFree.card_edgeFinset_le?>
:::

**Proposition (Turán number).** Write $n = qr + s$ with $0 \le s < r$. Then
$$t(n, r) = \frac{(r - 1)(n^2 - s^2)}{2r} + \binom{s}{2}.$$
In particular, $t(n, 2) = \lfloor n^2/4 \rfloor$, $t(n, 3) = \lfloor n^2/3 \rfloor$, and $t(n, r) \le \left(1 - \frac{1}{r}\right) \frac{n^2}{2}$.

*Proof.* The graph $T(n, r)$ has $s$ parts of size $q + 1$ and $r - s$ parts of size $q$. Count the non-edges: they are the pairs inside a part. Thus
$$t(n, r) = \binom{n}{2} - s\binom{q+1}{2} - (r - s)\binom{q}{2}.$$
Substitute $n = qr + s$ and simplify. The difference $n^2 - s^2 = qr(qr + 2s)$ is divisible by $r$, and a short computation gives the formula. For the bound, the sum of $\binom{|P_i|}{2}$ over $r$ parts with $\sum |P_i| = n$ is at least $r \binom{n/r}{2}$ by convexity, so
$$t(n, r) \le \binom{n}{2} - r \cdot \frac{(n/r)(n/r - 1)}{2} = \frac{n^2}{2}\Big(1 - \frac{1}{r}\Big). \quad \square$$

::: mathlib
`SimpleGraph.turanNumber_two` · `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`

`turanNumber_two : turanNumber n 2 = n ^ 2 / 4`, with natural division. Together with `SimpleGraph.CliqueFree.card_edgeFinset_le` for `r = 2`, it gives the theorem of Mantel: a triangle-free graph has at most `card V ^ 2 / 4` edges. The general formula is `SimpleGraph.turanNumber_eq`, `turanNumber n r = (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2`. The case $r = 3$ is `SimpleGraph.turanNumber_three`, and the bound $2 r \cdot t(n, r) \le (r-1) n^2$ is `SimpleGraph.mul_turanNumber_le`.

<?decl SimpleGraph.turanNumber_two?>
:::

### Examples

**Example (Small Turán numbers).** For $n = 7$ and $r = 3$, the parts have sizes $3, 2, 2$. The edges are $3 \cdot 2 + 3 \cdot 2 + 2 \cdot 2 = 16$. The formula gives $s = 1$ and $(2 \cdot 48)/6 + 0 = 16$, and $\lfloor 49/3 \rfloor = 16$. For $n = 5$ and $r = 2$, the graph is $K_{2,3}$ with $6 = \lfloor 25/4 \rfloor$ edges. Thus each graph on $5$ vertices with $7$ edges has a triangle.

**Example (A party problem).** At a meeting of $10$ persons, $26$ pairs know each other. Then three persons know each other in pairs, because $26 > t(10, 2) = 25$. With $25$ pairs this conclusion can fail. By the uniqueness part of Turán, it fails only when the persons split into two groups of $5$ and each person knows exactly the $5$ persons of the other group.

**Example (Clique number of a Turán graph).** The graph $T(n, r)$ with $n \ge r \ge 1$ has clique number exactly $r$: one vertex from each residue class gives an $r$-clique, and the proposition above excludes $r + 1$. The independent sets of maximum size are the largest parts, of size $\lceil n/r \rceil$.

**Example (Edges force cliques in Lean).** To show that a graph `G` on a finite type with `card V ^ 2 / 4 < #G.edgeFinset` has a triangle, apply `SimpleGraph.CliqueFree.card_edgeFinset_le` with `r = 2` in contrapositive form, and rewrite with `SimpleGraph.turanNumber_two`. The result is `¬G.CliqueFree 3`, and unfolding `SimpleGraph.CliqueFree` gives a finset `t` with `G.IsNClique 3 t`.

### The library around it

`Mathlib.Combinatorics.SimpleGraph.Clique` has cliques, $n$-cliques, clique-free graphs, the clique number and the independent sets, together with their finset versions `SimpleGraph.cliqueFinset` and `SimpleGraph.indepSetFinset`. `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic` has the predicate `SimpleGraph.IsExtremal` and the extremal numbers for an arbitrary forbidden graph. `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan` has the Turán graphs, the theorem of Turán and the Turán numbers. The Turán graph is complete multipartite, and the link to `SimpleGraph.completeMultipartiteGraph` is in `Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite`. The previous section gives the colouring of the Turán graph with $r$ colours and the inequality `SimpleGraph.cliqueNum_le_chromaticNumber`. The index of this edition has no declaration for the theorem of Erdős and Stone on $\operatorname{ex}(n, H)$ for a graph $H$ with chromatic number at least $3$.

Common errors of a learner:

- `G.IsClique s` takes a `Set`, and `G.IsNClique n s` takes a `Finset`. A finset `s` is coerced in `G.IsClique s`, so `SimpleGraph.isNClique_iff` mixes the two forms.
- A triangle is a `3`-clique, so "triangle-free" is `G.CliqueFree 3`, not `G.CliqueFree 2`. In general, "no $K_{r+1}$" is `G.CliqueFree (r + 1)`, which is the form that `SimpleGraph.IsTuranMaximal r` uses.
- `turanNumber n 2 = n ^ 2 / 4` uses natural division, so it is $\lfloor n^2/4 \rfloor$. A proof that needs the real bound must cast with care.
- `turanGraph n 0` is the complete graph, not the empty graph. Most theorems about Turán graphs need `0 < r`.

### Exercises

1. (A) Show that a graph on $V$ has an $n$-clique if and only if its complement has an independent set of size $n$.
2. (A) Find $t(6, 2)$, $t(6, 3)$, $t(8, 3)$ and $t(9, 4)$, and draw $T(8, 3)$.
3. (A) Show that the five-cycle has the most edges among the triangle-free graphs on $5$ vertices that are not bipartite. Show that it is not Turán-maximal for $r = 2$.
4. (B) Prove Mantel by induction on $n$. Delete the two ends of an edge and count the edges between them and the rest.
5. (B) Prove the edge bound of Turán by induction on $n$. Take a maximal clique $K$ of size $r$ and count the edges that leave $K$.
6. (B) Show that a graph with $n$ vertices and $m$ edges has an independent set of size at least $n^2/(2m + n)$. Hint: apply Turán to the complement. Compare with the bound of Caro and Wei, $\sum_v 1/(d(v) + 1)$.
7. (B) Show that a triangle-free graph on $n$ vertices with $\lfloor n^2/4 \rfloor$ edges is $K_{\lfloor n/2 \rfloor, \lceil n/2 \rceil}$, using only the proof of Mantel given above. Find the cases of equality in each inequality.
8. (C) Show that $\operatorname{ex}(n, C_4) \le \frac{n}{4}\big(1 + \sqrt{4n - 3}\big)$. Hint: count the pairs of edges at a common vertex, and use that two vertices have at most one common neighbour.
9. (C) The Motzkin-Straus theorem says that the maximum of $\sum_{u \sim v} x_u x_v$ over the probability vectors $x$ on $V$ is $\frac{1}{2}(1 - 1/\omega(G))$. Prove it, and deduce the edge bound of Turán.

### Notes and history

Mantel posed the triangle problem in 1907, in the problems section of the journal Wiskundige Opgaven, and the solution by Mantel and others appeared there. Turán proved his theorem in 1941, during forced labour, and asked in the same paper for the extremal numbers of other graphs, for example the graphs of the Platonic solids. This question started extremal graph theory. Erdős and Stone proved in 1946 that $\operatorname{ex}(n, H) = \left(1 - \frac{1}{\chi(H) - 1}\right)\binom{n}{2} + o(n^2)$, and Erdős and Simonovits noted in 1966 that this formula determines the extremal number asymptotically for each $H$ with $\chi(H) \ge 3$. For bipartite $H$ the formula gives only $o(n^2)$, and the exact order is open for most bipartite graphs, for example $C_8$ and $K_{4,4}$. The symmetrisation proof is due to Zykov in 1949. The Motzkin-Straus proof dates from 1965. The headers list Yaël Dillies and Bhavik Mehta for `Mathlib.Combinatorics.SimpleGraph.Clique`, Mitchell Horner for `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic`, and Jeremy Tan for `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`.

### Reference

<?reference?>
