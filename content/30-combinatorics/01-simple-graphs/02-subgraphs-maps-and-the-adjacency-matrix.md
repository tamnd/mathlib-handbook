---
title: Subgraphs, maps and the adjacency matrix
kind: theory
modules:
  - Mathlib.Combinatorics.SimpleGraph.Subgraph
  - Mathlib.Combinatorics.SimpleGraph.Maps
  - Mathlib.Combinatorics.SimpleGraph.DeleteEdges
  - Mathlib.Combinatorics.SimpleGraph.Copy
  - Mathlib.Combinatorics.SimpleGraph.AdjMatrix
explains:
  E3: [SimpleGraph.Subgraph, SimpleGraph.induce, SimpleGraph.deleteEdges, SimpleGraph.Hom, SimpleGraph.Iso, SimpleGraph.Copy, SimpleGraph.adjMatrix, SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
  E2: [SimpleGraph.Subgraph.verts, SimpleGraph.Subgraph.Adj, SimpleGraph.Subgraph.IsSpanning, SimpleGraph.Subgraph.IsInduced, SimpleGraph.Subgraph.induce, SimpleGraph.Subgraph.coe, SimpleGraph.Subgraph.spanningCoe, SimpleGraph.Subgraph.deleteVerts, SimpleGraph.Subgraph.degree, SimpleGraph.deleteEdges_adj, SimpleGraph.edgeSet_deleteEdges, SimpleGraph.edgeFinset_deleteEdges, SimpleGraph.Embedding, SimpleGraph.Hom.map_adj, SimpleGraph.Embedding.map_adj_iff, SimpleGraph.Iso.map_adj_iff, SimpleGraph.Iso.degree_eq, SimpleGraph.Iso.card_edgeFinset_eq, SimpleGraph.map, SimpleGraph.comap, SimpleGraph.IsContained, SimpleGraph.Free, SimpleGraph.IsIndContained, SimpleGraph.Copy.ofLE, SimpleGraph.Copy.injective, SimpleGraph.adjMatrix_apply, SimpleGraph.isSymm_adjMatrix, SimpleGraph.trace_adjMatrix, SimpleGraph.adjMatrix_mul_self_apply_self, SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.adjMatrix_mulVec_const_apply_of_regular, SimpleGraph.adjMatrix_mul_apply, Matrix.IsAdjMatrix, Matrix.IsAdjMatrix.toGraph, SimpleGraph.toGraph_adjMatrix_eq]
  E1: auto
families: []
requires: [V03.C03, V03.C06, V07.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Subgraphs, maps and the adjacency matrix

### Overview

This section compares graphs. A subgraph keeps some vertices and some edges of a graph. A homomorphism sends vertices to vertices and edges to edges. An isomorphism is a homomorphism with an inverse homomorphism, and isomorphic graphs have the same degrees and the same number of edges. A copy of $H$ in $G$ is an injective homomorphism, and it is the notion behind the statement "$G$ contains $H$" in Chapter 3.

The second half of the section turns a finite graph into a matrix. The adjacency matrix $A$ has the entry $1$ at $(v, w)$ when $v \sim w$ and $0$ otherwise. It is symmetric with zero diagonal, the diagonal of $A^2$ holds the degrees, and the entry $(A^n)_{uv}$ counts the walks of length $n$ from $u$ to $v$. For the Petersen graph these facts give the identity $A^2 + A - 2I = J$, where $J$ is the matrix of ones, and from it the eigenvalues. Section 1 of this chapter is assumed throughout.

### Definitions

**Definition (Subgraph).** Let $G$ be a graph on $V$. A subgraph $H$ of $G$ is a set $W \subseteq V$ of vertices and a symmetric relation $\mathrm{Adj}_H$ on $V$ such that $\mathrm{Adj}_H(v, w)$ implies $\mathrm{Adj}_G(v, w)$, $v \in W$ and $w \in W$. The subgraph is spanning when $W = V$. It is induced when it keeps every edge of $G$ between its vertices: $v, w \in W$ and $v \sim_G w$ imply $\mathrm{Adj}_H(v, w)$.

For each $W \subseteq V$ there is exactly one induced subgraph with vertex set $W$. It is the induced subgraph $G[W]$, and its edges are the edges of $G$ with both ends in $W$. Deleting the vertices of a set $S$ gives $G[V \setminus S]$. Deleting a set $S \subseteq \mathrm{Sym}^2 V$ of edges gives the spanning subgraph $G \setminus S$ with $v \sim w$ when $v \sim_G w$ and $s(v, w) \notin S$.

::: mathlib
`SimpleGraph.Subgraph` · `Mathlib.Combinatorics.SimpleGraph.Subgraph`

`G.Subgraph` is a structure with the fields `verts : Set V`, `Adj : V → V → Prop`, `adj_sub` (each edge is an edge of `G`), `edge_vert` (an edge has its ends in `verts`) and `symm`. The relation lives on all of `V`, and the vertex set is a separate field. So two subgraphs of `G` live in the same type and form a complete lattice. A subgraph becomes a graph in two ways: `H.coe` is a graph on the subtype `↥H.verts`, and `H.spanningCoe` is a graph on `V` with the same edges. The predicates `H.IsSpanning` and `H.IsInduced` are the two definitions above, `G'.induce s` is the induced subgraph on `s`, `H.deleteVerts s` removes vertices, and `H.degree v` is the degree inside `H`.

<?decl SimpleGraph.Subgraph?>
:::

::: mathlib
`SimpleGraph.induce` · `Mathlib.Combinatorics.SimpleGraph.Maps`

`SimpleGraph.induce s G : SimpleGraph ↥s` is $G[s]$ as a graph on the subtype. Use it to study the induced graph on its own, and the subgraph form `SimpleGraph.Subgraph.induce` to compare several subgraphs of the same `G`.

<?decl SimpleGraph.induce?>
:::

::: mathlib
`SimpleGraph.deleteEdges` · `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`

`G.deleteEdges s : SimpleGraph V` for `s : Set (Sym2 V)`, with `SimpleGraph.deleteEdges_adj : (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s`. The edge set is `G.edgeSet \ s` (`SimpleGraph.edgeSet_deleteEdges`), and `SimpleGraph.edgeFinset_deleteEdges` is the `Finset` form. The result is a graph on the same type `V`, not a `Subgraph`.

<?decl SimpleGraph.deleteEdges?>
:::

**Definition (Homomorphism, embedding, isomorphism).** Let $G$ be a graph on $V$ and $H$ a graph on $W$. A homomorphism $f : G \to H$ is a map $f : V \to W$ with $f(v) \sim_H f(w)$ whenever $v \sim_G w$. An embedding is an injective map with $f(v) \sim_H f(w)$ if and only if $v \sim_G w$. An isomorphism is a bijection with the same property. Then $G \cong H$.

**Definition (Copy).** A copy of $H$ in $G$ is an injective homomorphism $H \to G$. The graph $G$ contains $H$ when a copy exists, and $G$ is $H$-free when none exists. A copy need not be an embedding: a copy of $H$ may have more edges between its vertices in $G$ than in $H$.

::: mathlib
`SimpleGraph.Hom` · `Mathlib.Combinatorics.SimpleGraph.Maps`

`G →g H` is `SimpleGraph.Hom G H`, an abbreviation for the relation homomorphisms `RelHom G.Adj H.Adj`. In the same way `G ↪g H` (`SimpleGraph.Embedding`) is `RelEmbedding G.Adj H.Adj`, and `G ≃g H` is `RelIso G.Adj H.Adj`. The basic facts are `SimpleGraph.Hom.map_adj`, `SimpleGraph.Embedding.map_adj_iff` and `SimpleGraph.Iso.map_adj_iff`.

<?decl SimpleGraph.Hom?>
:::

::: mathlib
`SimpleGraph.Copy` · `Mathlib.Combinatorics.SimpleGraph.Copy`

`H.Copy G` is a structure with a homomorphism `toHom : H →g G` and a proof that it is injective (`SimpleGraph.Copy.injective`). `H ⊑ G` is `SimpleGraph.IsContained H G`, that is `Nonempty (H.Copy G)`, and `H.Free G` is its negation. For `G₁ ≤ G₂` on the same type, `SimpleGraph.Copy.ofLE` is the identity copy. The induced version is `SimpleGraph.IsIndContained`, written `G ⊴ H`, the existence of an embedding. These names give the statements of extremal graph theory in Chapter 3.

<?decl SimpleGraph.Copy?>
:::

**Definition (Adjacency matrix).** Let $V$ be finite. The adjacency matrix of $G$ is the $V \times V$ matrix $A$ with $A_{vw} = 1$ when $v \sim w$ and $A_{vw} = 0$ otherwise. Its entries lie in any semiring.

::: mathlib
`SimpleGraph.adjMatrix` · `Mathlib.Combinatorics.SimpleGraph.AdjMatrix`

`G.adjMatrix α : Matrix V V α` for `[DecidableRel G.Adj]` and a type `α` with `0` and `1`. The entry is `if G.Adj v w then 1 else 0` (`SimpleGraph.adjMatrix_apply`). The ring is a parameter so that the same matrix can be read in `ℕ`, in `ℤ` for eigenvalue arguments, or in `ZMod 2`. The predicate `Matrix.IsAdjMatrix` describes the matrices that arise: symmetric, entries in $\{0, 1\}$, zero diagonal. `Matrix.IsAdjMatrix.toGraph` turns such a matrix back into a graph, and `SimpleGraph.toGraph_adjMatrix_eq` says that the two constructions are inverse.

<?decl SimpleGraph.adjMatrix?>
:::

### Theorems and proofs

**Proposition (Isomorphisms keep degrees and edges).** Let $f : G \cong H$ be an isomorphism of locally finite graphs. Then $\deg_H(f(v)) = \deg_G(v)$ for each vertex $v$. If the graphs are finite, then $|E(G)| = |E(H)|$.

*Proof.* The map $f$ sends $N_G(v)$ into $N_H(f(v))$, since $w \sim v$ gives $f(w) \sim f(v)$. Its inverse $f^{-1}$ is also an isomorphism, so it sends $N_H(f(v))$ into $N_G(v)$. The two maps are inverse to each other, so $f$ restricts to a bijection $N_G(v) \to N_H(f(v))$, and the two sets have the same size. For the edges, the map $s(v, w) \mapsto s(f(v), f(w))$ is well defined on $\mathrm{Sym}^2 V$, it sends $E(G)$ into $E(H)$, and the same map for $f^{-1}$ is its inverse. $\square$

::: mathlib
`SimpleGraph.Iso` · `Mathlib.Combinatorics.SimpleGraph.Maps`

`G ≃g H`. The proposition is `SimpleGraph.Iso.degree_eq` and `SimpleGraph.Iso.card_edgeFinset_eq`, both in `Mathlib.Combinatorics.SimpleGraph.Finite`. An isomorphism is a bijection of the vertex types, so it is used to move a statement from a concrete type such as `Fin 10` to an abstract one.

<?decl SimpleGraph.Iso?>
:::

**Proposition (Basic facts on the adjacency matrix).** Let $A$ be the adjacency matrix of a finite graph $G$. Then $A^{T} = A$, $\operatorname{tr} A = 0$, and $(A^2)_{vv} = \deg(v)$ for each $v$. For a vector $x : V \to \alpha$, $(Ax)_v = \sum_{w \in N(v)} x_w$.

*Proof.* Symmetry: $A_{vw} = 1$ if and only if $v \sim w$, if and only if $w \sim v$, if and only if $A_{wv} = 1$. The trace is $\sum_v A_{vv} = 0$, since $v \not\sim v$. For the product with $x$,
$$(Ax)_v = \sum_{w \in V} A_{vw} x_w = \sum_{w \in N(v)} x_w,$$
since the terms with $w \notin N(v)$ are zero. The diagonal of $A^2$ is the case $x_w = A_{wv}$: by symmetry
$$(A^2)_{vv} = \sum_{w \in N(v)} A_{wv} = \sum_{w \in N(v)} 1 = \deg(v). \qquad \square$$

Summing the last identity over $v$ and using the degree-sum formula gives $\operatorname{tr}(A^2) = 2|E(G)|$. The matrix facts are those of Volume 7, Chapter 3.

**Theorem (Walks and powers of the adjacency matrix).** Let $G$ be finite. A walk of length $n$ from $u$ to $v$ is a sequence $u = v_0, v_1, \ldots, v_n = v$ with $v_{i-1} \sim v_i$ for $1 \le i \le n$. Let $w_n(u, v)$ be the number of these walks. Then $(A^n)_{uv} = w_n(u, v)$ for all $n \ge 0$.

*Proof.* Induction on $n$. For $n = 0$, $A^0 = I$, and the only walk of length $0$ is the sequence $(u)$, which ends at $v$ exactly when $u = v$. So $w_0(u, v) = I_{uv}$. For the step, sort the walks of length $n+1$ from $u$ to $v$ by their second vertex $v_1 = w$. A walk with $v_1 = w$ is the step $u \sim w$ followed by a walk of length $n$ from $w$ to $v$, and each such pair gives one walk. So
$$w_{n+1}(u, v) = \sum_{w \in N(u)} w_n(w, v) = \sum_{w \in V} A_{uw} (A^n)_{wv} = (A^{n+1})_{uv},$$
by the induction hypothesis and the formula for $(Ax)_u$ with $x = (A^n)_{\cdot v}$. $\square$

Chapter 2, Section 1 defines walks as an inductive type with the same two cases as this proof: the empty walk and a step followed by a walk. The theorem then counts the elements of a finite type of walks.

::: mathlib
`SimpleGraph.adjMatrix_pow_apply_eq_card_walk` · `Mathlib.Combinatorics.SimpleGraph.AdjMatrix`

`(G.adjMatrix α ^ n) u v = Fintype.card {p : G.Walk u v | p.length = n}`, cast into any semiring `α`. The other facts of the proposition are `SimpleGraph.isSymm_adjMatrix`, `SimpleGraph.trace_adjMatrix`, `SimpleGraph.adjMatrix_mul_self_apply_self` and `SimpleGraph.adjMatrix_mulVec_apply`. For a $d$-regular graph, `SimpleGraph.adjMatrix_mulVec_const_apply_of_regular` says that the constant vector is an eigenvector with eigenvalue $d$. The general product is `SimpleGraph.adjMatrix_mul_apply`. The trace is `Matrix.trace` of `Mathlib.LinearAlgebra.Matrix.Trace`.

<?decl SimpleGraph.adjMatrix_pow_apply_eq_card_walk?>
:::

### Examples

**Example (A 5-cycle inside the Petersen graph).** Use the description of Section 1. The vertices $\{1,2\}, \{3,4\}, \{1,5\}, \{2,3\}, \{4,5\}$ form a cycle in this order: each is disjoint from the next, and $\{4,5\}$ is disjoint from $\{1,2\}$. The other five pairs among them meet, for instance $\{1,2\}$ and $\{1,5\}$. So the induced subgraph on these five vertices is a 5-cycle. The other five vertices $\{1,3\}, \{2,4\}, \{3,5\}, \{1,4\}, \{2,5\}$ also induce a 5-cycle in this order. Each outer vertex has exactly one neighbour in the inner cycle: the neighbours of $\{1,2\}$ are $\{3,4\}, \{4,5\}$ and $\{3,5\}$, and only $\{3,5\}$ is inner. So the 15 edges are 5 outer, 5 inner and 5 between, which is the usual drawing as a pentagon and a pentagram.

**Example (The spectrum of the Petersen graph).** Let $A$ be its adjacency matrix. By the walk theorem, $(A^2)_{uv}$ is the number of common neighbours of $u$ and $v$ when $u \neq v$. Section 1 found this number: $0$ for adjacent vertices, $1$ for non-adjacent ones. With $(A^2)_{uu} = 3$, this gives
$$A^2 = 3I + (J - I - A), \qquad \text{that is} \qquad A^2 + A - 2I = J.$$
The graph is 3-regular, so $A\mathbf{1} = 3\mathbf{1}$ for the vector of ones. Let $x$ be an eigenvector of the real symmetric matrix $A$ orthogonal to $\mathbf{1}$, with $Ax = \lambda x$. Then $Jx = 0$, so $(\lambda^2 + \lambda - 2)x = 0$ and $\lambda \in \{1, -2\}$. Let $a$ and $b$ be the multiplicities of $1$ and $-2$. Then $1 + a + b = 10$, and $\operatorname{tr} A = 0$ gives $3 + a - 2b = 0$. So $a = 5$ and $b = 4$. As a check, $\operatorname{tr}(A^2) = 9 + 5 \cdot 1 + 4 \cdot 4 = 30 = 2 \cdot 15$. The spectral theorem used here is in Volume 7, Chapter 5.

**Counterexample (A copy that is not induced).** Let $P_3$ be the path $a \sim b \sim c$ and let $K_3$ be the triangle on $\{1, 2, 3\}$. The map $a \mapsto 1$, $b \mapsto 2$, $c \mapsto 3$ is an injective homomorphism, so $K_3$ contains a copy of $P_3$. It is not an embedding, since $1 \sim 3$ but $a \not\sim c$. In fact $K_3$ has no induced $P_3$: any three vertices of $K_3$ induce $K_3$. In the language of the library, $P_3 \sqsubseteq K_3$ holds and the induced containment fails.

### The library around it

Mathlib has two notions of a smaller graph. A `Subgraph` of `G` has its own vertex set and lives in the lattice `G.Subgraph`. A graph `H : SimpleGraph V` with `H ≤ G` has all the vertices of `G` and lives in the lattice of graphs on `V`. Spanning subgraphs correspond to the second notion through `spanningCoe`. For $f : V \to W$, the graph `SimpleGraph.comap f H` on $V$ pulls back the edges of $H$, and `SimpleGraph.map f G` on $W$ pushes forward the edges of $G$.

Common errors of a learner:

- `H.coe` is a graph on the subtype `↥H.verts`. Its vertices are pairs of a vertex and a proof of membership, so a vertex `v : V` must be packed as `⟨v, hv⟩` before it is used.
- `G →g H` asks only that edges go to edges. Two adjacent vertices never have the same image, but two non-adjacent vertices may.
- `G.adjMatrix α` needs the ring `α` explicitly. The equation `(A * A) v v = G.degree v` holds in any non-associative semiring, but the cast from `ℕ` appears on the right side.
- In `SimpleGraph.Copy H G` the small graph `H` comes first. In `H.Free G` the same is true: the statement is that `G` contains no copy of `H`.

### Exercises

1. (A) Show that the induced subgraph of $K_n$ on any $k$ vertices is $K_k$, and that the induced subgraph of the empty graph is empty.
2. (A) Show that the composition of two homomorphisms is a homomorphism and that the identity is an isomorphism $G \cong G$.
3. (A) Show that there is a homomorphism from the 5-cycle to $K_3$, and no homomorphism from $K_3$ to the 5-cycle. Hint: adjacent vertices have different images.
4. (A) Let $A$ be the adjacency matrix of $K_n$. Show that $A = J - I$ and compute $A^2$. Hint: $J^2 = nJ$.
5. (B) Show that $\operatorname{tr}(A^3) = 6t$, where $t$ is the number of triangles of $G$. Hint: a closed walk of length 3 runs around a triangle, from one of 3 starts in one of 2 directions.
6. (B) Show that the Petersen graph has no triangle by computing $\operatorname{tr}(A^3)$ from its spectrum.
7. (B) Let $G$ be $d$-regular on $n$ vertices. Show that $A$ commutes with $J$.
8. (B) Let $G$ be a graph on $n$ vertices with $A^2 + A - (d-1)I = J$ for some $d$. Show that $G$ is $d$-regular and that adjacent vertices have no common neighbour.
9. (C) Show that a graph is isomorphic to its complement only if $n \equiv 0$ or $1 \pmod 4$, and give such graphs for $n = 4$ and $n = 5$.

### Notes and history

The adjacency matrix and the count of walks by its powers are the start of spectral graph theory. Biggs, *Algebraic Graph Theory* (1974), and Godsil and Royle, *Algebraic Graph Theory* (2001), treat this subject. The identity $A^2 + A - (d-1)I = J$ describes the Moore graphs of diameter 2, and Hoffman and Singleton showed in 1960 by the argument of the second example that these exist only for $d \in \{2, 3, 7, 57\}$. The Petersen graph is the case $d = 3$. The headers of the files `Mathlib.Combinatorics.SimpleGraph.Subgraph` and `Mathlib.Combinatorics.SimpleGraph.Maps` list Hunter Monroe and Kyle Miller, with Alena Gusakov for subgraphs. The header of `Mathlib.Combinatorics.SimpleGraph.Copy` lists Yaël Dillies and Mitchell Horner.

### Reference

<?reference?>
