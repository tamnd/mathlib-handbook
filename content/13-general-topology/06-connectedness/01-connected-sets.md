---
title: Connected sets and the intermediate value theorem
kind: theory
modules:
  - Mathlib.Topology.Connected.Basic
  - Mathlib.Topology.Connected.Clopen
  - Mathlib.Topology.Order.IntermediateValue
explains:
  E3: [IsPreconnected, IsConnected, connectedComponent]
  E2: [PreconnectedSpace, ConnectedSpace, IsClopen, isClopen_iff, preconnectedSpace_iff_clopen, isPreconnected_closed_iff, IsPreconnected.image, IsConnected.image, isPreconnected_Icc, isConnected_Icc, isPreconnected_iff_ordConnected, intermediate_value_Icc, IsPreconnected.intermediate_value, IsPreconnected.closure, IsConnected.closure, IsPreconnected.union, isPreconnected_sUnion, IsPreconnected.subset_connectedComponent, isClosed_connectedComponent, isConnected_connectedComponent, TotallyDisconnectedSpace, IsPreconnected.prod]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Connected sets and the intermediate value theorem

### Overview

A set is connected if it cannot be split by two open sets into two nonempty disjoint parts. Continuous maps send connected sets to connected sets. In $\mathbb{R}$, the connected sets are exactly the intervals. Together, these two facts give the intermediate value theorem. This section proves them and gives the rules that build new connected sets from old ones.

Mathlib separates two notions. A preconnected set satisfies the splitting condition, and the empty set is preconnected. A connected set is a nonempty preconnected set. Most theorems are stated for preconnected sets, because the empty case then needs no special hypothesis.

### Definitions

**Definition (Preconnected, connected).** A subset $S$ of a topological space $X$ is preconnected if for all open sets $U, V$ with $S \subseteq U \cup V$, $S \cap U \neq \emptyset$ and $S \cap V \neq \emptyset$, the set $S \cap U \cap V$ is nonempty. It is connected if it is also nonempty. The space $X$ is (pre)connected if $X$ is a (pre)connected subset of itself.

::: mathlib
`IsPreconnected` · `Mathlib.Topology.Connected.Basic`

The definition above, with open sets of `X`. The open sets need not be disjoint in `X`; only their trace on `S` matters. `IsConnected s` is `s.Nonempty ∧ IsPreconnected s`. The space versions are the classes `PreconnectedSpace` and `ConnectedSpace`.

<?decl IsPreconnected?>
:::

::: mathlib
`IsConnected` · `Mathlib.Topology.Connected.Basic`

A nonempty preconnected set.

<?decl IsConnected?>
:::

**Definition (Clopen).** A set is clopen if it is both closed and open.

::: mathlib
`IsClopen` · `Mathlib.Topology.Defs.Basic`

The conjunction `IsClosed s ∧ IsOpen s`. The lemma `isClopen_iff` says that in a preconnected space the only clopen sets are `∅` and `univ`, and `preconnectedSpace_iff_clopen` is the converse.

<?decl IsClopen?>
:::

**Definition (Connected component).** The connected component of a point $x$ is the union of all preconnected sets that contain $x$.

::: mathlib
`connectedComponent` · `Mathlib.Topology.Connected.Basic`

The union of the preconnected sets that contain `x`. It is connected (`isConnected_connectedComponent`), closed (`isClosed_connectedComponent`), and it contains each preconnected set through `x` (`IsPreconnected.subset_connectedComponent`). A space is totally disconnected (`TotallyDisconnectedSpace`) if each component is a point.

<?decl connectedComponent?>
:::

### Theorems and proofs

**Theorem (Clopen sets).** A space $X$ is preconnected if and only if its only clopen sets are $\emptyset$ and $X$.

*Proof.* Let $X$ be preconnected and $A$ clopen. The sets $A$ and $X \setminus A$ are open, disjoint, and cover $X$. If both were nonempty, preconnectedness would give a point in $A \cap (X \setminus A)$. So $A = \emptyset$ or $A = X$. Conversely, suppose that $U \cup V = X$ with $U, V$ open, nonempty and disjoint. Then $U = X \setminus V$ is closed and open, and it is neither $\emptyset$ nor $X$. $\square$

**Theorem (Images).** Let $f : X \to Y$ be continuous and $S \subseteq X$ preconnected. Then $f(S)$ is preconnected.

*Proof.* Let $U, V$ be open in $Y$ with $f(S) \subseteq U \cup V$, and let $f(S)$ meet both. Then $S \subseteq f^{-1}(U) \cup f^{-1}(V)$, the preimages are open, and $S$ meets both. So some $x \in S$ lies in $f^{-1}(U) \cap f^{-1}(V)$, and $f(x) \in f(S) \cap U \cap V$. $\square$

::: mathlib
`IsPreconnected.image` · `Mathlib.Topology.Connected.Basic`

The theorem, with `ContinuousOn f s` in place of continuity on the whole space. `IsConnected.image` is the connected version.

<?decl IsPreconnected.image?>
:::

**Theorem (Intervals are connected).** Each interval $[a, b]$ of $\mathbb{R}$ is preconnected.

*Proof.* Let $U, V$ be open with $[a, b] \subseteq U \cup V$. Suppose that $[a, b]$ meets both, and that $[a, b] \cap U \cap V = \emptyset$. Choose $u \in [a, b] \cap U$ and $v \in [a, b] \cap V$; by symmetry let $u < v$. Let $c = \sup \{ t \in [u, v] : t \in U \}$. Then $u \le c \le v$.

Suppose $c \in U$. Then $c \neq v$, since $v \in V$ and $v \notin U$. As $U$ is open, $(c - \delta, c + \delta) \subseteq U$ for some $\delta > 0$, and then a point of $(c, \min(c + \delta, v))$ lies in $U \cap [u, v]$. This contradicts the choice of $c$.

Suppose $c \in V$. Then $c \neq u$. As $V$ is open, $(c - \delta, c] \subseteq V$ for some $\delta > 0$, and these points are not in $U$. So $c - \delta$ is an upper bound of $\{ t \in [u, v] : t \in U \}$, smaller than $c$. This contradicts the choice of $c$.

Since $c \in U \cup V$, both cases fail. So $[a, b] \cap U \cap V$ is nonempty. $\square$

The same argument works for each interval and in each conditionally complete linear order with a dense order topology. Conversely, a preconnected subset $S$ of $\mathbb{R}$ is an interval: if $a < c < b$ with $a, b \in S$ and $c \notin S$, the open sets $(-\infty, c)$ and $(c, \infty)$ split $S$.

::: mathlib
`isPreconnected_Icc` · `Mathlib.Topology.Order.IntermediateValue`

The theorem, in a densely ordered conditionally complete linear order. The characterisation of all preconnected sets is `isPreconnected_iff_ordConnected`: a set is preconnected if and only if it contains the interval between each two of its points.

<?decl isPreconnected_Icc?>
:::

**Corollary (Intermediate value theorem).** Let $f : [a, b] \to \mathbb{R}$ be continuous and $y$ between $f(a)$ and $f(b)$. Then $f(c) = y$ for some $c \in [a, b]$.

*Proof.* The image $f([a, b])$ is preconnected, so it is an interval. It contains $f(a)$ and $f(b)$, so it contains $y$. $\square$

::: mathlib
`intermediate_value_Icc` · `Mathlib.Topology.Order.IntermediateValue`

For `a ≤ b` and `f` continuous on `Icc a b`, the interval `Icc (f a) (f b)` lies in `f '' Icc a b`. The general form `IsPreconnected.intermediate_value` takes a preconnected set in any space and a map to an order topology.

<?decl intermediate_value_Icc?>
:::

**Theorem (Closure and unions).** Let $S$ be preconnected.

1. Each $T$ with $S \subseteq T \subseteq \overline{S}$ is preconnected. In particular $\overline{S}$ is preconnected.
2. If $(S_i)$ are preconnected sets that all contain one point $x$, then $\bigcup_i S_i$ is preconnected.

*Proof.* 1. Let $U, V$ be open, $T \subseteq U \cup V$, and $T$ meet both $U$ and $V$. A point of $T \cap U$ lies in $\overline{S}$, and $U$ is an open neighbourhood of it, so $S \cap U \neq \emptyset$. In the same way $S \cap V \neq \emptyset$. As $S \subseteq U \cup V$, preconnectedness of $S$ gives a point in $S \cap U \cap V \subseteq T \cap U \cap V$.

2. Let $W = \bigcup_i S_i$. Let $U, V$ be open with $W \subseteq U \cup V$, $W \cap U \ni u$ and $W \cap V \ni v$. Then $x \in U$ or $x \in V$; let $x \in U$. Choose $i$ with $v \in S_i$. Then $S_i$ meets $U$ at $x$ and $V$ at $v$, so $S_i \cap U \cap V$ is nonempty. $\square$

So the connected component of $x$ is preconnected by part 2 and closed by part 1, since its closure is a preconnected set through $x$. Two components are equal or disjoint: if $z$ lies in both, their union is preconnected by part 2, so each contains the other.

::: mathlib
`IsPreconnected.closure` · `Mathlib.Topology.Connected.Basic`

Part 1 for the closure. `IsConnected.closure` is the connected version.

<?decl IsPreconnected.closure?>
:::

::: mathlib
`isPreconnected_sUnion` · `Mathlib.Topology.Connected.Basic`

Part 2: a union of preconnected sets that all contain `x` is preconnected. `IsPreconnected.union` is the case of two sets.

<?decl isPreconnected_sUnion?>
:::

**Theorem (Products).** If $S \subseteq X$ and $T \subseteq Y$ are preconnected, then $S \times T$ is preconnected.

*Proof.* The empty cases are clear. For $(s, t), (s', t') \in S \times T$, the set $(\{s\} \times T) \cup (S \times \{t'\})$ is preconnected by part 2 of the last theorem, since both pieces are images of preconnected sets and both contain $(s, t')$. It contains the two points. A set in which each two points lie in a common preconnected subset is preconnected, by the same argument as part 2. $\square$

::: mathlib
`IsPreconnected.prod` · `Mathlib.Topology.Connected.Basic`

The theorem for binary products. `isPreconnected_univ_pi` covers arbitrary products.

<?decl IsPreconnected.prod?>
:::

### Examples

**Example (The rationals).** The space $\mathbb{Q}$ is totally disconnected. If $S \subseteq \mathbb{Q}$ contains $a < b$, choose an irrational $c$ between them. The open sets $\{x < c\}$ and $\{x > c\}$ split $S$. So each component is a single point. The discrete topology on $\mathbb{Q}$ has the same components but more open sets, so total disconnectedness does not determine the topology.

**Example (The cofinite topology).** An infinite set $X$ with the cofinite topology is connected. Two nonempty open sets have finite complements, so their intersection has finite complement and is nonempty. The same argument shows that each infinite subset is connected.

**Counterexample (Removing a point).** The interval $(0, 1)$ minus the point $1/2$ is not connected. The circle $S^1$ minus a point is connected, since it is the image of an open interval. So $(0, 1)$ and $S^1$ are not homeomorphic: a homeomorphism would map $(0, 1) \setminus \{1/2\}$ to $S^1$ minus a point.

### The library around it

The definitions and the closure and union rules are in `Mathlib.Topology.Connected.Basic`. The characterisations with clopen sets and with disjoint open sets are in `Mathlib.Topology.Connected.Clopen`. The facts on intervals and the intermediate value theorem are in `Mathlib.Topology.Order.IntermediateValue`. Totally disconnected and totally separated spaces are in `Mathlib.Topology.Connected.TotallyDisconnected`.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that a continuous map from a connected space to a discrete space is constant.
2. (A) Show that $\mathbb{R}^2 \setminus \{0\}$ is connected, and deduce that it is not homeomorphic to $\mathbb{R}$.
3. (A) Show that a space with the indiscrete topology is connected.
4. (B) Show that each continuous map $f : [0, 1] \to [0, 1]$ has a fixed point.
5. (B) Show that in a space with finitely many components each component is open. Give a space where a component is not open.
6. (B) Show that if $S$ is connected and $A$ is a set with $S \cap A \neq \emptyset$ and $S \setminus A \neq \emptyset$, then $S$ meets the boundary of $A$.
7. (C) Show that a connected metric space with at least two points is uncountable. Hint: use the map $x \mapsto d(x, x_0)$.

### Notes and history

Cantor gave a metric definition of connected sets in 1883, and Jordan used connectedness for compact plane sets. The definition with open sets is due to Lennes (1905) and Riesz (1907), and Hausdorff's *Grundzüge der Mengenlehre* (1914) made it standard. The intermediate value theorem goes back to Bolzano (1817). Authors differ on whether the empty set is connected. Mathlib avoids the question with two names: the empty set is preconnected and not connected.

### Reference

<?reference?>
