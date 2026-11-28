---
title: Hamiltonian walks, cycle graphs and girth
kind: api
modules:
  - Mathlib.Combinatorics.SimpleGraph.Hamiltonian
  - Mathlib.Combinatorics.SimpleGraph.Hamiltonian.Perm
  - Mathlib.Combinatorics.SimpleGraph.CycleGraph
  - Mathlib.Combinatorics.SimpleGraph.Girth
explains:
  E2: [SimpleGraph.Walk.IsHamiltonian.length_eq, SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq, SimpleGraph.IsHamiltonian.exists_isHamiltonianCycle, SimpleGraph.not_isHamiltonian_of_card_eq_two, SimpleGraph.cycleGraph_degree_three_le, SimpleGraph.three_le_egirth, SimpleGraph.egirth_le_two_mul_ediam_add_one]
  E1: auto
families: []
requires: [V30.C01, V03.C03, V03.C06, V05.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Hamiltonian walks, cycle graphs and girth

### Overview

Section 1 of this chapter studies walks that use each edge at most once and proves the theorem of Euler on trails through every edge. This section studies the dual question for vertices. A Hamiltonian path visits each vertex of the graph exactly once, and a Hamiltonian cycle is a cycle through all the vertices. No simple test for the existence of a Hamiltonian cycle is known, in contrast with the degree test of Euler. The library has the definitions, the basic invariance properties, and the link with the cycle graphs: a graph on $n \ge 3$ vertices is Hamiltonian if and only if it contains a copy of the cycle $C_n$.

The section then defines the cycle graph $C_n$ on `Fin n`, and the girth of a graph, the length of a shortest cycle. The girth and the diameter of Section 2 bound each other: a connected graph with a cycle has girth at most $2 \operatorname{diam} + 1$. The section uses the walks of Section 1 and the tools of Section 4, in particular `SimpleGraph.Walk.rotate`, `SimpleGraph.Walk.tail` and the maps of walks.

### The library around it

#### Hamiltonian paths

The module `Mathlib.Combinatorics.SimpleGraph.Hamiltonian` works over a vertex type `α` with `DecidableEq α`, since it counts vertices in lists. A walk `p` is Hamiltonian when each vertex of `α` occurs exactly once in its support: `SimpleGraph.Walk.IsHamiltonian p` is `∀ a, p.support.count a = 1`. The definition does not ask for a path, but a path follows: no vertex repeats (`SimpleGraph.Walk.IsHamiltonian.isPath`). Conversely a path through all vertices is Hamiltonian (`SimpleGraph.Walk.IsPath.isHamiltonian_of_mem`), and `SimpleGraph.Walk.isHamiltonian_iff_isPath_and_forall_mem_support` states the two directions together.

A Hamiltonian walk lists the whole vertex type, so the type is finite (`SimpleGraph.Walk.IsHamiltonian.finite`, and `SimpleGraph.Walk.not_isHamiltonian_of_infinite`). The list of vertices of the walk is then a bijection from positions to vertices. The library gives it as two equivalences `Fin p.support.length ≃ α`: `SimpleGraph.Walk.IsHamiltonian.supportGetEquiv` reads the list, and `SimpleGraph.Walk.IsHamiltonian.getVertEquiv` uses `p.getVert`.

**Theorem.** Let $\alpha$ be finite with $n$ elements. A Hamiltonian walk has length $n - 1$.

*Proof.* Each vertex occurs once in the support, so the support is a list of length $n$ (`SimpleGraph.Walk.IsHamiltonian.length_support`). The length of a walk is the length of its support minus one. $\square$

This is `SimpleGraph.Walk.IsHamiltonian.length_eq`, and `SimpleGraph.Walk.isHamiltonian_iff_isPath_and_length_eq` gives the converse for paths: a path of length $n - 1$ visits $n$ distinct vertices, which are all the vertices. A Hamiltonian walk stays Hamiltonian under the operations of Section 4 that keep the vertex type: `SimpleGraph.Walk.IsHamiltonian.reverse`, `SimpleGraph.Walk.IsHamiltonian.mapLe`, `SimpleGraph.Walk.IsHamiltonian.transfer` and `SimpleGraph.Walk.IsHamiltonian.copy`, each with an `iff` form. Along a homomorphism `f` the property needs `f` bijective (`SimpleGraph.Walk.isHamiltonian_map`). A Hamiltonian path makes the graph connected (`SimpleGraph.Walk.IsHamiltonian.connected`).

#### Hamiltonian cycles

A closed walk `p : G.Walk a a` is a Hamiltonian cycle when it is a cycle and its tail is a Hamiltonian walk. The structure `SimpleGraph.Walk.IsHamiltonianCycle` extends `SimpleGraph.Walk.IsCycle` with the field `isHamiltonian_tail`. The tail drops the first vertex, which reappears at the end, so the condition says that each vertex occurs once in the cycle. The start $a$ occurs twice in the support and every other vertex once (`SimpleGraph.Walk.IsHamiltonianCycle.count_support_self`, `SimpleGraph.Walk.IsHamiltonianCycle.support_count_of_ne`).

**Theorem.** Let $\alpha$ be finite with $n$ elements. A closed walk is a Hamiltonian cycle if and only if it is a cycle of length $n$.

*Proof.* Let `p` be a Hamiltonian cycle. Its tail is a Hamiltonian walk, of length $n - 1$ by the theorem above, so `p` has length $n$. Conversely, let `p` be a cycle of length $n$. The tail of its support has $n$ entries and no repetition, since `p` is a cycle. So it contains each of the $n$ vertices once, and the tail of `p` is Hamiltonian. $\square$

This is `SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq`, and `SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq_natCard` is the form with `Nat.card`. A Hamiltonian cycle can start at any vertex: `SimpleGraph.Walk.IsHamiltonianCycle.rotate` moves the start, and `SimpleGraph.Walk.IsHamiltonianCycle.reverse` reverses the direction. The cycle also gives a Hamiltonian path in two ways, by `SimpleGraph.Walk.IsHamiltonianCycle.isHamiltonian_tail` and `SimpleGraph.Walk.IsHamiltonianCycle.isHamiltonian_dropLast`.

#### Hamiltonian graphs

A finite graph is Hamiltonian when it has a Hamiltonian cycle. The definition `SimpleGraph.IsHamiltonian G` needs `Fintype α` and reads `Fintype.card α ≠ 1 → ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle`. This fixes two conventions. The graph on one vertex is Hamiltonian (`SimpleGraph.IsHamiltonian.of_card_eq_one`), although it has no cycle. The graph on no vertex is not Hamiltonian (`SimpleGraph.not_isHamiltonian_of_isEmpty`), since no start vertex exists.

**Theorem.** If $G$ is Hamiltonian and has at least two vertices, then each vertex $v$ is the start of a Hamiltonian cycle.

*Proof.* The definition gives a Hamiltonian cycle `p` at some vertex $a$. The vertex $v$ is in the support of `p`, since every vertex is. The rotation `p.rotate v` is a closed walk at $v$, and it is a Hamiltonian cycle by `SimpleGraph.Walk.IsHamiltonianCycle.rotate`. $\square$

This is `SimpleGraph.IsHamiltonian.exists_isHamiltonianCycle`. A Hamiltonian graph is connected (`SimpleGraph.IsHamiltonian.connected`), and more edges keep the property (`SimpleGraph.IsHamiltonian.mono`).

**Theorem.** No graph on exactly two vertices is Hamiltonian.

*Proof.* A cycle has length at least $3$ (Section 1), and a Hamiltonian cycle on $n$ vertices has length $n$. So $n \ge 3$. $\square$

This is `SimpleGraph.not_isHamiltonian_of_card_eq_two`. A bridge, an edge whose deletion disconnects its ends, also excludes a Hamiltonian cycle (`SimpleGraph.IsBridge.not_isHamiltonian`): a cycle through both ends of a bridge would give a second route between them. The complete graph on $n$ vertices is Hamiltonian if and only if $n = 1$ or $n \ge 3$ (`SimpleGraph.isHamiltonian_top_iff`). A Hamiltonian cycle with its first edge removed is a Hamiltonian path whose ends are adjacent. The converse is `SimpleGraph.Walk.IsHamiltonian.isHamiltonian_of_adj`: a Hamiltonian path from $a$ to $b$ with $a \sim b$ and length different from $1$ closes to a Hamiltonian cycle. The case of length $1$ is the graph $K_2$, where the closing edge is the edge of the path. `SimpleGraph.isHamiltonian_iff_exists_adj_and_isHamiltonian` states the equivalence on a nontrivial type.

The module `Mathlib.Combinatorics.SimpleGraph.Hamiltonian.Perm` reads a Hamiltonian cycle as a permutation. Let $\sigma$ be a cyclic permutation of $\alpha$ in the sense of `Equiv.Perm.IsCycle` that moves along edges: $v \sim \sigma(v)$ for all $v$. If $\alpha$ has at least $3$ elements, then $G$ is Hamiltonian (`SimpleGraph.IsHamiltonian.of_perm`). The walk $v, \sigma(v), \sigma^2(v), \ldots$ returns to $v$ after $n$ steps and visits each vertex once. The relative form `SimpleGraph.cycleGraph_isContained_of_isCycleOn` takes $\sigma$ cyclic on a finset $s$ and gives a copy of $C_{|s|}$ in $G$.

#### Cycle graphs

The module `Mathlib.Combinatorics.SimpleGraph.CycleGraph` defines `SimpleGraph.cycleGraph n` on `Fin n`. For $n \ge 2$ two vertices $a, b$ are adjacent when $a - b = 1$ or $b - a = 1$ in `Fin n`, that is modulo $n$ (`SimpleGraph.cycleGraph_adj`). For $n = 0$ and $n = 1$ the graph is `⊥`. So `cycleGraph n` is the cycle $C_n$ only for $n \ge 3$. The graph `cycleGraph 2` is a single edge, and `cycleGraph 3` is the triangle; both are the complete graph (`SimpleGraph.cycleGraph_two_eq_top`, `SimpleGraph.cycleGraph_three_eq_top`, and in general `SimpleGraph.cycleGraph_eq_top_iff`). The neighbours of $v$ are $v - 1$ and $v + 1$ (`SimpleGraph.cycleGraph_neighborFinset`).

**Theorem.** For $n \ge 3$ every vertex of $C_n$ has degree $2$.

*Proof.* The neighbours of $v$ are $v - 1$ and $v + 1$. They are different, because $v - 1 = v + 1$ means $2 = 0$ in `Fin n`, which fails for $n \ge 3$. $\square$

This is `SimpleGraph.cycleGraph_degree_three_le`, stated for `Fin (n + 3)`. The cycle graph is connected for $n \ge 1$ (`SimpleGraph.connected_cycleGraph_add_one`). The walk `SimpleGraph.cycleGraph.cycle n` goes once around `cycleGraph (n + 3)` from $0$ to $0$. It is a cycle of length $n + 3$ through every vertex (`SimpleGraph.cycleGraph.isCycle_cycle`, `SimpleGraph.cycleGraph.length_cycle`, `SimpleGraph.cycleGraph.mem_support_cycle`). So it is a Hamiltonian cycle (`SimpleGraph.Walk.IsHamiltonianCycle.cycleGraph_cycle`), and `SimpleGraph.isHamiltonian_cycleGraph_iff` states that $C_n$ is Hamiltonian if and only if $n = 1$ or $n \ge 3$.

Cycles of a graph and copies of cycle graphs are the same thing. For $n \ge 3$, `cycleGraph n` is contained in $G$ if and only if $G$ has a cycle of length $n$ (`SimpleGraph.cycleGraph_isContained_iff`). With $n$ the number of vertices this gives `SimpleGraph.isHamiltonian_iff_cycleGraph_isContained`: a graph on $n \ge 3$ vertices is Hamiltonian if and only if it contains a copy of $C_n$. The chromatic number of $C_n$ is in Chapter 3.

#### Girth

The module `Mathlib.Combinatorics.SimpleGraph.Girth` defines two forms of the girth. The extended girth `G.egirth : ℕ∞` is the infimum of the lengths of the cycles of $G$. A graph with no cycle has `G.egirth = ⊤` (`SimpleGraph.egirth_eq_top`), since the infimum of the empty set is the top element. The girth `G.girth : ℕ` is `G.egirth.toNat` (`SimpleGraph.girth_eq_toNat_egirth`), so it is $0$ for an acyclic graph (`SimpleGraph.girth_eq_zero`). The value $0$ stands for $\infty$ here, in the same way as `SimpleGraph.dist` in Section 2.

The characterizations are `SimpleGraph.le_egirth`, a lower bound for all cycle lengths, and `SimpleGraph.Walk.IsCycle.egirth_le_length`, the upper bound by one cycle. A graph with a cycle has a shortest cycle (`SimpleGraph.exists_egirth_eq_length`, `SimpleGraph.exists_girth_eq_length`), since the lengths are natural numbers.

**Theorem.** The extended girth of every graph is at least $3$.

*Proof.* Each cycle has length at least $3$, so $3$ is a lower bound of the set of lengths, and `SimpleGraph.le_egirth` applies. For an acyclic graph the girth is $\top \ge 3$. $\square$

This is `SimpleGraph.three_le_egirth`, and `SimpleGraph.three_le_girth` is the form for `girth` under the hypothesis `¬G.IsAcyclic`. The girth goes down when the graph grows: `SimpleGraph.egirth_anti` states that `egirth` is antitone, and `SimpleGraph.IsContained.egirth_le` states the same for a copy of one graph in another. Isomorphic graphs have the same girth (`SimpleGraph.Iso.egirth_eq`, `SimpleGraph.Iso.girth_eq`). The complete graph on at least $3$ vertices has girth $3$ (`SimpleGraph.girth_top`), and the empty graph has girth $0$ (`SimpleGraph.girth_bot`).

**Theorem.** A graph with a cycle satisfies $g(G) \le 2 \operatorname{diam}(G) + 1$, with the extended diameter.

*Proof sketch.* Assume the diameter $D$ is finite, else there is nothing to prove. Let $C$ be a shortest cycle, of length $g$, and assume $g \ge 2D + 2$. Choose two vertices $x, y$ of $C$ at distance $D + 1$ along $C$. Both arcs of $C$ between $x$ and $y$ have length at least $D + 1$. A shortest walk $P$ from $x$ to $y$ in $G$ has length at most $D$, so it differs from both arcs. The walk $P$ followed by the arc of length $D + 1$ back to $x$ is a closed walk of length at most $2D + 1 < g$. It is not a walk that only goes forth and back along a tree, since $P$ differs from the arc, so it contains a cycle. This contradicts the choice of $C$. $\square$

This is `SimpleGraph.egirth_le_two_mul_ediam_add_one`, and `SimpleGraph.girth_le_two_mul_ediam_add_one` and `SimpleGraph.girth_le_two_mul_diam_add_one` are the forms with `girth` and with the finite diameter. The Petersen graph has diameter $2$ and girth $5$, so it attains the bound.

#### Common errors

1. A learner states a fact about `G.IsHamiltonian` on a type with no `Fintype` instance or no `DecidableEq` instance. The definition needs both. On a graph with one vertex the statement is true by convention, so a theorem about Hamiltonian cycles often needs `Nontrivial α` or `3 ≤ Fintype.card α`.
2. A learner reads `cycleGraph 2` as a cycle of length $2$. Simple graphs have no such cycle: `cycleGraph 2` is one edge, and `cycleGraph 0` and `cycleGraph 1` are empty graphs.
3. A learner reads `G.girth = 0` as a small girth. It means that $G$ is acyclic. Use `G.egirth`, with the value `⊤`, in statements that must cover forests.

### Exercises

1. (A) Show that the complete bipartite graph $K_{m,n}$ with $m \ne n$ has no Hamiltonian cycle.
2. (A) Compute the girth of $K_n$, of $K_{m,n}$ for $m, n \ge 2$, of $C_n$ for $n \ge 3$ and of a tree.
3. (A) Use `SimpleGraph.IsHamiltonian.of_perm` with the permutation $v \mapsto v + 1$ of `Fin n` to show that $C_n$ is Hamiltonian for $n \ge 3$.
4. (B) Show that a Hamiltonian graph has no vertex of degree $1$, and that a graph with a cut vertex is not Hamiltonian.
5. (B) Show that the Petersen graph has no Hamiltonian cycle. Hint: a Hamiltonian cycle $C$ leaves a perfect matching of $5$ edges outside $C$, and the girth $5$ restricts where these edges can be.
6. (C) Let $G$ be a $d$-regular graph with $d \ge 2$ and girth $5$. Show that $G$ has at least $d^2 + 1$ vertices.

### Reference

<?reference?>
