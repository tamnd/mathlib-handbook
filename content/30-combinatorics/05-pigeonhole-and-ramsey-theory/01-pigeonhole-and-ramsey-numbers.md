---
title: Pigeonhole and Ramsey numbers
kind: theory
modules:
  - Mathlib.Combinatorics.Pigeonhole
  - Mathlib.Combinatorics.Compactness
  - Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
explains:
  E3: [Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to, SimpleGraph.EdgeLabeling, SimpleGraph.TopEdgeLabeling, SimpleGraph.EdgeLabeling.labelGraph, SimpleGraph.card_topEdgeLabeling, Finset.rado_selection]
  E2: [Fintype.exists_lt_card_fiber_of_mul_lt_card, Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to, Fintype.exists_le_card_fiber_of_mul_le_card, Finset.exists_card_fiber_lt_of_card_lt_mul, Finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to, Finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum, Nat.exists_lt_modEq_of_infinite, SimpleGraph.EdgeLabeling.get, SimpleGraph.EdgeLabeling.mk, SimpleGraph.EdgeLabeling.pullback, SimpleGraph.EdgeLabeling.labelGraph_adj, SimpleGraph.TopEdgeLabeling.labelGraph_adj, SimpleGraph.toTopEdgeLabeling, SimpleGraph.toTopEdgeLabeling_labelGraph, SimpleGraph.toTopEdgeLabeling_labelGraph_compl, SimpleGraph.EdgeLabeling.pairwise_disjoint_labelGraph, SimpleGraph.EdgeLabeling.iSup_labelGraph, Set.Finite.rado_selection, Finset.rado_selection_subtype, Set.Finite.rado_selection_subtype]
  E1: auto
families: []
requires: [V30.C01, V30.C03, V03.C03, V03.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pigeonhole and Ramsey numbers

### Overview

The pigeonhole principle says that if many objects go into few boxes, some box gets many objects. Ramsey theory applies this idea again and again. Colour the edges of a large complete graph red and blue. Then some large set of vertices has all its edges in one colour. Complete disorder is impossible in a large enough structure.

This section starts from the pigeonhole principle of Volume 3, Chapter 3. It proves the theorem of Erdős and Szekeres on monotone subsequences, Ramsey's theorem for graphs with the bound $R(s,t) \le \binom{s+t-2}{s-1}$, the value $R(3,3) = 6$, and the lower bound of Erdős by counting. It ends with the infinite Ramsey theorem and the compactness principle that connects the infinite and the finite theorems.

The index of this edition has no declaration for Ramsey's theorem for graphs. The proofs below are on paper, and the boxes show the parts that Mathlib has: colourings of edges and a compactness principle.

### Definitions

**Definition (Edge colouring).** Let $G$ be a simple graph on $V$ and $K$ a set of colours. A $K$-*colouring of the edges* of $G$ is a map from the edge set of $G$ to $K$. A set $S \subseteq V$ is *monochromatic of colour* $k$ if each edge of the complete graph on $S$ is an edge of $G$ of colour $k$.

A colouring of the edges of the complete graph $K_n$ with two colours is the same as a graph $H$ on $n$ vertices: the red edges form $H$ and the blue edges form its complement $H^c$. A red set is a clique of $H$, and a blue set is an independent set of $H$.

**Definition (Ramsey number).** For $s, t \ge 1$ the *Ramsey number* $R(s,t)$ is the least $n$ such that each red and blue colouring of the edges of $K_n$ has a red set of size $s$ or a blue set of size $t$.

The theorem below shows that $R(s,t)$ exists. A set of one vertex is both red and blue, so $R(1, t) = R(s, 1) = 1$. In a colouring of $K_n$ with no blue edge the whole vertex set is red, and a single blue edge is a blue pair. So $R(s, 2) = s$, and by symmetry $R(2, t) = t$. Also $R(s,t) = R(t,s)$, by an exchange of the colours.

::: mathlib
`SimpleGraph.EdgeLabeling` · `Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling`

`G.EdgeLabeling K` is the type `G.edgeSet → K` of maps from the edges to the colours. The function `EdgeLabeling.get C x y h` reads the colour of the edge $xy$ from a proof `h : G.Adj x y`, and `EdgeLabeling.mk` builds a colouring from a symmetric function of the two ends. The function `EdgeLabeling.pullback` restricts a colouring along a graph homomorphism.

<?decl SimpleGraph.EdgeLabeling?>
:::

::: mathlib
`SimpleGraph.TopEdgeLabeling` · `Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling`

`TopEdgeLabeling V K` is `EdgeLabeling (⊤ : SimpleGraph V) K`, a colouring of the edges of the complete graph on `V`. For a graph `G`, `G.toTopEdgeLabeling` is the colouring by `Fin 2` with colour 1 on the edges of `G` and colour 0 on the other pairs. The lemmas `toTopEdgeLabeling_labelGraph` and `toTopEdgeLabeling_labelGraph_compl` recover `G` and its complement.

<?decl SimpleGraph.TopEdgeLabeling?>
:::

::: mathlib
`SimpleGraph.EdgeLabeling.labelGraph` · `Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling`

`C.labelGraph k` is the graph of the edges of colour `k`. The graphs for different colours are disjoint (`pairwise_disjoint_labelGraph`), and their supremum is `G` (`iSup_labelGraph`). A set is monochromatic of colour `k` exactly when it is a clique of `C.labelGraph k`, in the sense of Chapter 3.

<?decl SimpleGraph.EdgeLabeling.labelGraph?>
:::

### Theorems and proofs

The strong form of the pigeonhole principle is in Volume 3, Chapter 3: if $f$ maps a finite set $s$ into a finite set $t$ and $|t| \cdot n < |s|$, then some fibre of $f$ has more than $n$ elements. The proofs below use it without comment.

::: mathlib
`Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to` · `Mathlib.Combinatorics.Pigeonhole`

If `∀ a ∈ s, f a ∈ t` and `t.card * n < s.card`, then `∃ y ∈ t, n < {x ∈ s | f x = y}.card`. The file has the variants with `≤` (`exists_le_card_fiber_of_mul_le_card_of_maps_to`), with sums of weights (`exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum`) and for a whole finite type (`Fintype.exists_lt_card_fiber_of_mul_lt_card`). The lemma `Nat.exists_lt_modEq_of_infinite` is an infinite form for residues.

<?decl Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to?>
:::

**Theorem (Erdős and Szekeres).** Let $r, s \ge 1$. Each sequence of $rs + 1$ distinct real numbers has an increasing subsequence of length $r + 1$ or a decreasing subsequence of length $s + 1$.

*Proof.* Let the sequence be $x_1, \dots, x_{rs+1}$. For each $i$ let $a_i$ be the length of the longest increasing subsequence that ends at $x_i$, and $d_i$ the length of the longest decreasing subsequence that ends at $x_i$. Let $i < j$. If $x_i < x_j$, then $x_j$ extends each increasing subsequence that ends at $x_i$, so $a_j > a_i$. If $x_i > x_j$, then $d_j > d_i$ in the same way. So the pairs $(a_i, d_i)$ are distinct. Suppose that $a_i \le r$ and $d_i \le s$ for each $i$. Then there are at most $rs$ possible pairs for $rs + 1$ indices, and two indices share a pair, which is impossible. So some $a_i \ge r + 1$ or some $d_i \ge s + 1$. $\square$

The bound is sharp. For $r = s = 2$ the sequence $2, 1, 4, 3$ has four terms, no increasing subsequence of length 3 and no decreasing subsequence of length 3.

**Theorem (Ramsey for graphs).** For $s, t \ge 2$,
$$R(s, t) \le R(s - 1, t) + R(s, t - 1).$$
Hence $R(s,t)$ exists for all $s, t \ge 1$, and $R(s, t) \le \binom{s + t - 2}{s - 1}$.

*Proof.* Assume that $R(s-1, t)$ and $R(s, t-1)$ exist, and let $n = R(s-1, t) + R(s, t-1)$. Colour the edges of $K_n$ red and blue. Fix a vertex $v$. Let $A$ be the set of the other ends of the red edges at $v$ and $B$ the set of the other ends of the blue edges. Then $|A| + |B| = n - 1$. If $|A| \le R(s-1,t) - 1$ and $|B| \le R(s, t-1) - 1$, then $n - 1 \le n - 2$, which is false. So $|A| \ge R(s-1, t)$ or $|B| \ge R(s, t-1)$.

In the first case, $A$ contains a red set of size $s - 1$ or a blue set of size $t$. A blue set of size $t$ finishes the proof. A red set $S$ of size $s - 1$ gives the red set $S \cup \{v\}$ of size $s$, since all edges from $v$ to $A$ are red. The second case is the same with the colours exchanged. This proves the inequality, and the existence of all $R(s,t)$ follows by induction on $s + t$, from the values $R(1, t) = R(s, 1) = 1$.

For the binomial bound, use induction on $s + t$. If $s = 1$ or $t = 1$, both sides are $1$. Otherwise, by the inequality and Pascal's rule,
$$R(s,t) \le \binom{s+t-3}{s-2} + \binom{s+t-3}{s-1} = \binom{s+t-2}{s-1}. \qquad \square$$

**Theorem ($R(3,3) = 6$).** Each red and blue colouring of the edges of $K_6$ has a monochromatic triangle, and some colouring of $K_5$ has none.

*Proof.* Take a colouring of $K_6$ and a vertex $v$. Five edges meet $v$, so three of them have the same colour, by pigeonhole with $2 \cdot 2 < 5$. Say $va$, $vb$ and $vc$ are red. If one of $ab$, $bc$, $ca$ is red, it forms a red triangle with $v$. Otherwise $abc$ is a blue triangle.

For $K_5$, take the vertices $0, \dots, 4$, colour $ij$ red when $j - i \equiv \pm 1 \pmod 5$ and blue when $j - i \equiv \pm 2 \pmod 5$. The red graph is the 5-cycle $0, 1, 2, 3, 4$. The blue graph is the 5-cycle $0, 2, 4, 1, 3$. A cycle of length 5 contains no triangle, so no triangle is monochromatic. $\square$

The next result is a lower bound. It shows that some colouring has no large monochromatic set without constructing one.

**Theorem (Erdős).** For $k \ge 3$, $R(k, k) > 2^{k/2}$.

*Proof.* Let $n = \lfloor 2^{k/2} \rfloor$. If $n < k$, then $R(k,k) \ge k > n$, as no set of $k$ vertices exists in $K_n$. So assume $n \ge k$. There are $2^{\binom n2}$ colourings of the edges of $K_n$. Fix a set $S$ of $k$ vertices. The colourings in which $S$ is monochromatic fix the colour of $\binom k2$ edges to one of two values, so there are $2 \cdot 2^{\binom n2 - \binom k2}$ of them. A colouring is *bad* if some $S$ of size $k$ is monochromatic. The number of bad colourings is at most
$$\binom nk \cdot 2^{1 - \binom k2} \cdot 2^{\binom n2}.$$
Now $\binom nk \le n^k / k! \le 2^{k^2/2}/k!$, and $2^{1 - \binom k2} = 2^{1 - k^2/2 + k/2}$. So the fraction of bad colourings is at most $2^{1 + k/2}/k!$. For $k = 3$ this is $2^{5/2}/6 < 5.7/6 < 1$. When $k$ grows by one, the numerator is multiplied by $\sqrt 2$ and the denominator by $k + 1 \ge 4$, so the fraction stays below 1. Thus some colouring is not bad, and $R(k,k) > n$. Since $R(k,k)$ is an integer and $n = \lfloor 2^{k/2} \rfloor$, this gives $R(k,k) > 2^{k/2}$. $\square$

::: mathlib
`SimpleGraph.card_topEdgeLabeling` · `Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling`

For finite `V` and `K`, `Fintype.card (TopEdgeLabeling V K) = Fintype.card K ^ (Fintype.card V).choose 2`. This is the total count $2^{\binom n2}$ in the proof above, for `K = Fin 2`.

<?decl SimpleGraph.card_topEdgeLabeling?>
:::

**Theorem (Infinite Ramsey for pairs).** Colour the pairs of natural numbers with finitely many colours. Then some infinite set $X \subseteq \mathbb{N}$ has all its pairs of one colour.

*Proof.* Put $Y_0 = \mathbb{N}$. Suppose an infinite set $Y_i$ is given. Let $x_i$ be its least element. The pairs $\{x_i, y\}$ with $y \in Y_i \setminus \{x_i\}$ have finitely many colours, so by the infinite pigeonhole principle (Volume 3, Chapter 5) one colour $c_i$ occurs for infinitely many $y$. Let $Y_{i+1}$ be the set of these $y$. This defines $x_0 < x_1 < \dots$ and colours $c_0, c_1, \dots$. For $i < j$ the element $x_j$ lies in $Y_{i+1}$, so $\{x_i, x_j\}$ has colour $c_i$. Some colour $c$ equals $c_i$ for infinitely many $i$. The set $X$ of these $x_i$ is infinite, and each pair $\{x_i, x_j\}$ with $i < j$ in $X$ has colour $c_i = c$. $\square$

The finite theorem follows from the infinite one by a compactness principle. Mathlib states the principle in a form due to Rado.

**Theorem (Rado selection).** Let $\alpha$ be a set and $\beta(a)$ a finite set for each $a \in \alpha$. For each finite $s \subseteq \alpha$ let $g_s$ be a choice function with $g_s(a) \in \beta(a)$. Then there is a choice function $\chi$ such that for each finite $s$ there is a finite $t \supseteq s$ with $\chi = g_t$ on $s$.

The proof uses Tychonoff's theorem for the product of the finite sets $\beta(a)$, as in Section 1 of Chapter 4.

**Corollary (Finite Ramsey from infinite Ramsey).** For each $k$ and each finite number of colours, there is $n$ such that each colouring of the edges of $K_n$ has a monochromatic set of size $k$.

*Proof.* Suppose not. Then for each $n$ there is a colouring $h_n$ of the pairs of $\{0, \dots, n-1\}$ with no monochromatic set of size $k$. Let $\alpha$ be the set of pairs of natural numbers. For a finite set $s$ of pairs, let $N$ exceed every element of every pair in $s$, and let $g_s$ be $h_N$ on the pairs below $N$ and any colour elsewhere. Rado selection gives a colouring $\chi$ of all pairs. By the infinite theorem, $\chi$ has an infinite monochromatic set $X$. Take $k$ elements of $X$ and let $s$ be the set of their pairs. There is $t \supseteq s$ with $\chi = g_t$ on $s$, and $g_t$ is $h_N$ on $s$ for some $N$. So $h_N$ has a monochromatic set of size $k$, which is a contradiction. $\square$

::: mathlib
`Finset.rado_selection` · `Mathlib.Combinatorics.Compactness`

For `β : α → Type` with `[∀ a, Finite (β a)]` and `g : Finset α → (a : α) → β a`, the statement `∃ χ, ∀ s, ∃ t, s ⊆ t ∧ ∀ x ∈ s, χ x = g t x`. The version `Set.Finite.rado_selection` takes finite sets instead of finsets, and the `_subtype` versions take a function `g t` defined only on `t`.

<?decl Finset.rado_selection?>
:::

::: mathlib
`exists_increasing_or_nonincreasing_subseq` · `Mathlib.Order.OrderIsoNat`

For a transitive relation `r` and a sequence `f : ℕ → α`, there is a strictly increasing `g : ℕ ↪o ℕ` such that `r (f (g m)) (f (g n))` holds for all `m < n`, or fails for all `m < n`. It is infinite Ramsey for colourings that come from a transitive relation. With `r` equal to `<` on a linear order, it gives an infinite increasing or infinite non-increasing subsequence, the infinite form of Erdős and Szekeres. Its home is the volume on orders.

<?decl exists_increasing_or_nonincreasing_subseq?>
:::

### Examples

**Example (Small Ramsey numbers).** The values $R(3, 4) = 9$, $R(3, 5) = 14$ and $R(4, 4) = 18$ are known. The recursion gives $R(3, 4) \le R(2, 4) + R(3, 3) = 4 + 6 = 10$, one more than the true value. With $R(3,4) = 9$ it gives $R(4,4) \le 2 R(3, 4) = 18$, which is exact. The bound of Erdős gives only $R(4, 4) > 4$.

**Example (Counting the colourings of $K_4$).** By `card_topEdgeLabeling` there are $2^6 = 64$ colourings of the edges of $K_4$ with two colours. For a fixed triangle, $2 \cdot 2^3 = 16$ colourings make it monochromatic. There are 4 triangles, so at most $64$ colourings have a monochromatic triangle. The union bound gives nothing here: a colouring of $K_4$ without a monochromatic triangle exists by the $K_5$ example, but the count does not show it.

### The library around it

The file `Pigeonhole` has about forty forms of the principle; Volume 3, Chapter 3 explains how to choose among them.

The index of this edition has no declaration for Ramsey's theorem for graphs, for the numbers $R(s,t)$, or for the theorem of Erdős and Szekeres on finite sequences.

The file `Compactness` proves Rado's selection principle. Section 2 uses a different form of compactness, the compact space of ultrafilters.

### Exercises

1. (A) Show that among any $n + 1$ integers two have a difference divisible by $n$. Hint: residues modulo $n$.
2. (A) Show that $R(s, 2) = s$ directly from the definition.
3. (A) Find a sequence of 9 distinct numbers with no increasing and no decreasing subsequence of length 4.
4. (B) Show that each red and blue colouring of $K_6$ has at least two monochromatic triangles. Hint: count the pairs of edges of different colours at a vertex.
5. (B) Prove that $R(3, 4) \le 9$. Hint: in the proof of the recursion, both $R(2,4) = 4$ and $R(3,3) = 6$ are even. If $K_9$ has no red triangle and no blue $K_4$, show that each vertex has exactly 3 red edges, and count the ends of the red edges.
6. (B) Define $R(t_1, \dots, t_r)$ for $r$ colours and prove that it exists. Hint: merge two colours.
7. (B) Prove Schur's theorem: for each $r$ there is $N$ such that each colouring of $\{1, \dots, N\}$ with $r$ colours has a monochromatic solution of $x + y = z$. Hint: colour the edge $ij$ of $K_{N+1}$ by the colour of $|i - j|$.
8. (C) Show that $R(k,k) \le 4^k$ and $R(k,k) > 2^{k/2}$, and conclude that $\sqrt 2 \le \liminf R(k,k)^{1/k} \le \limsup R(k,k)^{1/k} \le 4$.
9. (C) Use Rado selection to prove that an infinite graph is $k$-colourable if each finite subgraph is $k$-colourable.

### Notes and history

Frank Ramsey proved the theorem in 1930 in a paper on formal logic. Erdős and Szekeres found it again in 1935 and proved the monotone subsequence theorem and the binomial bound. The values $R(3, 4) = 9$, $R(3, 5) = 14$ and $R(4, 4) = 18$ are due to Greenwood and Gleason (1955). Erdős proved the lower bound by counting in 1947, one of the first applications of the probabilistic method. The value of $R(5, 5)$ is not known.

The file `Pigeonhole` lists Kyle Miller and Yury Kudryashov as authors, `Compactness` lists Bhavik Mehta, and `SimpleGraph.Coloring.EdgeLabeling` lists Bhavik Mehta and Olivia Röhrig.

### Reference

<?reference?>
