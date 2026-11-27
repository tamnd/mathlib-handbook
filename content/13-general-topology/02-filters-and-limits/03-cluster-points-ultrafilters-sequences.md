---
title: Cluster points, ultrafilters and sequences
kind: theory
modules:
  - Mathlib.Topology.ClusterPt
  - Mathlib.Order.Filter.Ultrafilter.Defs
  - Mathlib.Topology.Ultrafilter
  - Mathlib.Topology.Sequences
  - Mathlib.Topology.Defs.Sequences
explains:
  E3: [ClusterPt, Ultrafilter, FrechetUrysohnSpace]
  E2: [MapClusterPt, ClusterPt.neBot, clusterPt_principal_iff, mem_closure_iff_clusterPt, mem_closure_iff_nhds, isClosed_iff_clusterPt, Ultrafilter.mem_or_compl_mem, Ultrafilter.em, Ultrafilter.of, Ultrafilter.of_le, Filter.exists_ultrafilter_le, Ultrafilter.map, Ultrafilter.clusterPt_iff, mem_closure_iff_ultrafilter, FirstCountableTopology.frechetUrysohnSpace, mem_closure_iff_seq_limit, tendsto_nhds_iff_seq_tendsto, IsSeqClosed, SequentialSpace, isSeqClosed_iff_isClosed]
  E1: auto
families: []
requires: [V04, V13.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cluster points, ultrafilters and sequences

### Overview

A sequence in $[0, 1]$ need not converge, but it has a convergent subsequence. Its limit is a point near which the sequence comes back again and again. For a filter, this notion is a cluster point: a point each of whose neighbourhoods meets each large set of the filter. Cluster points describe the closure of a set, and in Chapter 5 they define compactness.

An ultrafilter is a filter that cannot be refined. For each set, it contains the set or its complement. An ultrafilter has no room to oscillate, so an ultrafilter that has a cluster point converges to it. Each proper filter is contained in an ultrafilter, by Zorn's lemma. Ultrafilters play the part of subsequences, and they work in each space.

The section ends with sequences. In a first countable space, such as a metric space, sequences describe the closure and limits. In general they do not, and the filters are necessary.

### Definitions

**Definition (Cluster point).** Let $F$ be a filter on a space $X$. A point $x$ is a cluster point of $F$ if $\mathcal{N}(x) \sqcap F$ is proper, that is, if $N \cap A \ne \emptyset$ for each $N \in \mathcal{N}(x)$ and each $A \in F$. For a map $u : I \to X$ and a filter $F$ on $I$, $x$ is a cluster point of $u$ along $F$ if it is a cluster point of $u_{*}F$.

*Remarks.* For a sequence $u$ and $F = \mathrm{atTop}$, $x$ is a cluster point of $u$ if each neighbourhood of $x$ contains $u_n$ for infinitely many $n$. If $F \le \mathcal{N}(x)$, then $\mathcal{N}(x) \sqcap F = F$, so a limit of a proper filter is a cluster point.

::: mathlib
`ClusterPt` · `Mathlib.Topology.Defs.Filter`

`ClusterPt x F` is defined as `NeBot (𝓝 x ⊓ F)`. The lemma `ClusterPt.neBot` returns this fact.

<?decl ClusterPt?>
:::

::: mathlib
`ClusterPt.neBot` · `Mathlib.Topology.ClusterPt`

A cluster point gives the properness of `𝓝 x ⊓ F`.

<?decl ClusterPt.neBot?>
:::

::: mathlib
`MapClusterPt` · `Mathlib.Topology.Defs.Filter`

`MapClusterPt x F u` is `ClusterPt x (map u F)`. For a sequence: `MapClusterPt x atTop u`.

<?decl MapClusterPt?>
:::

**Definition (Ultrafilter).** An ultrafilter on $X$ is a proper filter $U$ such that for each $A \subseteq X$, $A \in U$ or $X \setminus A \in U$.

*Remarks.* Equivalently, $U$ is a minimal element of the proper filters in the order of Section 1: each proper filter $G \le U$ equals $U$. The principal filter $\mathcal{P}(\{x\})$ is an ultrafilter, the principal ultrafilter at $x$. On an infinite set there are other ultrafilters, but no explicit example: their existence needs the axiom of choice.

::: mathlib
`Ultrafilter` · `Mathlib.Order.Filter.Ultrafilter.Defs`

`Ultrafilter α` is a structure: a filter `toFilter` with the two fields `neBot'` and `le_of_le`, the second the minimality. It coerces to `Filter α`, and `s ∈ U` means membership in the underlying filter. The principal ultrafilter is `pure x`.

<?decl Ultrafilter?>
:::

::: mathlib
`Ultrafilter.mem_or_compl_mem` · `Mathlib.Order.Filter.Ultrafilter.Defs`

For each set, the set or its complement is in the ultrafilter.

<?decl Ultrafilter.mem_or_compl_mem?>
:::

::: mathlib
`Ultrafilter.em` · `Mathlib.Order.Filter.Ultrafilter.Defs`

The excluded middle along an ultrafilter: each property holds eventually or fails eventually.

<?decl Ultrafilter.em?>
:::

**Definition (Sequential closure, Fréchet-Urysohn space).** A set $A \subseteq X$ is sequentially closed if each limit of a sequence in $A$ is in $A$. The space $X$ is a Fréchet-Urysohn space if each point of the closure of a set $A$ is a limit of a sequence in $A$. It is a sequential space if each sequentially closed set is closed.

::: mathlib
`FrechetUrysohnSpace` · `Mathlib.Topology.Defs.Sequences`

The class says `closure s ⊆ seqClosure s` for each `s`. Each first countable space is an instance (`FirstCountableTopology.frechetUrysohnSpace`), and each Fréchet-Urysohn space is a sequential space.

<?decl FrechetUrysohnSpace?>
:::

::: mathlib
`IsSeqClosed` · `Mathlib.Topology.Defs.Sequences`

A set is sequentially closed if it contains the limit of each convergent sequence in it.

<?decl IsSeqClosed?>
:::

::: mathlib
`SequentialSpace` · `Mathlib.Topology.Defs.Sequences`

The class of spaces in which sequentially closed sets are closed.

<?decl SequentialSpace?>
:::

### Theorems and proofs

**Theorem (Closure by cluster points).** Let $A \subseteq X$ and $x \in X$. The following are equivalent.

1. $x \in \overline{A}$.
2. Each neighbourhood of $x$ meets $A$.
3. $x$ is a cluster point of $\mathcal{P}(A)$.
4. There is a proper filter $F$ with $A \in F$ and $F \le \mathcal{N}(x)$.

*Proof.* (1 ⇔ 2) Assume $x \in \overline{A}$ and let $N$ be a neighbourhood of $x$, with $x \in U \subseteq N$ and $U$ open. If $U \cap A = \emptyset$, then $A \subseteq X \setminus U$, a closed set, so $\overline{A} \subseteq X \setminus U$ and $x \notin \overline{A}$, a contradiction. Conversely, if $x \notin \overline{A}$, then $X \setminus \overline{A}$ is an open neighbourhood of $x$ that misses $A$.

(2 ⇔ 3) The members of $\mathcal{P}(A)$ are the supersets of $A$. So $N \cap B \ne \emptyset$ for each neighbourhood $N$ and each $B \supseteq A$ if and only if $N \cap A \ne \emptyset$ for each $N$.

(3 ⇒ 4) Take $F = \mathcal{N}(x) \sqcap \mathcal{P}(A)$. It is proper by 3, it contains $A$, and $F \le \mathcal{N}(x)$.

(4 ⇒ 2) Let $N \in \mathcal{N}(x)$. Then $N \in F$, so $N \cap A \in F$. Since $F$ is proper, $N \cap A \ne \emptyset$. $\square$

::: mathlib
`mem_closure_iff_clusterPt` · `Mathlib.Topology.ClusterPt`

Form 3 of the theorem.

<?decl mem_closure_iff_clusterPt?>
:::

::: mathlib
`mem_closure_iff_nhds` · `Mathlib.Topology.ClusterPt`

Form 2 of the theorem.

<?decl mem_closure_iff_nhds?>
:::

::: mathlib
`clusterPt_principal_iff` · `Mathlib.Topology.ClusterPt`

The equivalence of forms 2 and 3.

<?decl clusterPt_principal_iff?>
:::

::: mathlib
`isClosed_iff_clusterPt` · `Mathlib.Topology.ClusterPt`

A set is closed if and only if it contains each cluster point of its principal filter.

<?decl isClosed_iff_clusterPt?>
:::

**Theorem (Ultrafilter lemma).** Each proper filter $F$ on $X$ is contained in an ultrafilter: there is an ultrafilter $U$ with $U \le F$.

*Proof.* Let $P$ be the set of proper filters $G$ with $G \le F$, that is, $F \subseteq G$ as families. It contains $F$. Order $P$ by inclusion of families. Let $C \subseteq P$ be a nonempty chain. The union $\bigcup C$ is a filter. It contains $X$. It is closed under supersets. If $A \in G_1$ and $B \in G_2$ with $G_1, G_2 \in C$, then one of them, say $G_2$, contains the other, so $A \cap B \in G_2$. The union does not contain $\emptyset$, because no member of $C$ does. So $\bigcup C \in P$ is an upper bound of $C$. By Zorn's lemma $P$ has a maximal element $U$.

The filter $U$ is an ultrafilter. Let $A \subseteq X$ with $A \notin U$. Suppose that $X \setminus A \notin U$. Then each $B \in U$ meets $A$: if $B \cap A = \emptyset$, then $B \subseteq X \setminus A$ and $X \setminus A \in U$. So the filter generated by $U \cup \{A\}$, whose members contain the sets $B \cap A$ with $B \in U$, is proper. It is in $P$, it contains $U$, and it contains $A \notin U$. This contradicts the maximality of $U$. So $X \setminus A \in U$. $\square$

::: mathlib
`Filter.exists_ultrafilter_le` · `Mathlib.Order.Filter.Ultrafilter.Defs`

The theorem, for `f` with `[NeBot f]`. The choice is packaged as `Ultrafilter.of f`, with `Ultrafilter.of_le : ↑(Ultrafilter.of f) ≤ f`.

<?decl Filter.exists_ultrafilter_le?>
:::

::: mathlib
`Ultrafilter.of` · `Mathlib.Order.Filter.Ultrafilter.Defs`

A chosen ultrafilter below a proper filter.

<?decl Ultrafilter.of?>
:::

::: mathlib
`Ultrafilter.of_le` · `Mathlib.Order.Filter.Ultrafilter.Defs`

The chosen ultrafilter is finer than the filter.

<?decl Ultrafilter.of_le?>
:::

**Theorem (Images and cluster points of ultrafilters).** Let $U$ be an ultrafilter on $X$.

1. For $m : X \to Y$, the image $m_{*}U$ is an ultrafilter on $Y$.
2. If $X$ is a space, a point $x$ is a cluster point of $U$ if and only if $U \le \mathcal{N}(x)$.

*Proof.* (1) The image of a proper filter is proper, since $m^{-1}(\emptyset) = \emptyset \notin U$. Let $B \subseteq Y$. Then $m^{-1}(B) \in U$ or $X \setminus m^{-1}(B) = m^{-1}(Y \setminus B) \in U$, so $B \in m_{*}U$ or $Y \setminus B \in m_{*}U$.

(2) If $U \le \mathcal{N}(x)$, then $x$ is a cluster point, by the remark after the definition. Conversely, let $x$ be a cluster point and $N \in \mathcal{N}(x)$. If $N \notin U$, then $X \setminus N \in U$. But $N \cap (X \setminus N) = \emptyset$, which contradicts the cluster point property. So $N \in U$. $\square$

::: mathlib
`Ultrafilter.map` · `Mathlib.Order.Filter.Ultrafilter.Defs`

The image of an ultrafilter, as an ultrafilter. The coercion satisfies `↑(U.map m) = map m ↑U` (`Ultrafilter.coe_map`).

<?decl Ultrafilter.map?>
:::

::: mathlib
`Ultrafilter.clusterPt_iff` · `Mathlib.Topology.Ultrafilter`

Part 2 of the theorem: a cluster point of an ultrafilter is a limit of it.

<?decl Ultrafilter.clusterPt_iff?>
:::

::: mathlib
`mem_closure_iff_ultrafilter` · `Mathlib.Topology.Ultrafilter`

A point is in the closure of `s` if and only if some ultrafilter that contains `s` converges to it. This is form 4 of the closure theorem with an ultrafilter below `F`.

<?decl mem_closure_iff_ultrafilter?>
:::

**Theorem (Sequences in a first countable space).** Let $X$ be first countable, $A \subseteq X$ and $x \in X$. Then $x \in \overline{A}$ if and only if there is a sequence in $A$ that tends to $x$.

*Proof.* If $a_n \in A$ and $a_n \to x$, let $N$ be a neighbourhood of $x$. Then $a_n \in N$ for large $n$, so $N$ meets $A$, and $x \in \overline{A}$.

Conversely, let $x \in \overline{A}$. Let $(B_k)$ be a countable basis of $\mathcal{N}(x)$, and set $N_n = B_0 \cap \dots \cap B_n$. The sets $N_n$ decrease and form a basis of $\mathcal{N}(x)$. Each $N_n$ meets $A$, so choose $a_n \in N_n \cap A$. Let $N$ be a neighbourhood of $x$. Then $N_k \subseteq N$ for some $k$, and for $n \ge k$, $a_n \in N_n \subseteq N_k \subseteq N$. So $a_n \to x$. $\square$

::: mathlib
`mem_closure_iff_seq_limit` · `Mathlib.Topology.Sequences`

The theorem, for a Fréchet-Urysohn space. A first countable space is one by the instance below.

<?decl mem_closure_iff_seq_limit?>
:::

::: mathlib
`FirstCountableTopology.frechetUrysohnSpace` · `Mathlib.Topology.Sequences`

The proof of the theorem, as an instance.

<?decl FirstCountableTopology.frechetUrysohnSpace?>
:::

::: mathlib
`tendsto_nhds_iff_seq_tendsto` · `Mathlib.Topology.Sequences`

In a Fréchet-Urysohn space, `f` tends to `b` at `a` if and only if `f (u n)` tends to `b` for each sequence `u` that tends to `a`. This is the sequential criterion of analysis.

<?decl tendsto_nhds_iff_seq_tendsto?>
:::

::: mathlib
`isSeqClosed_iff_isClosed` · `Mathlib.Topology.Sequences`

In a sequential space, sequentially closed and closed agree.

<?decl isSeqClosed_iff_isClosed?>
:::

### Examples

**Example (Cluster points of a sequence).** Let $u_n = (-1)^n + 1/(n+1)$ in $\mathbb{R}$. The image filter $u_{*}\mathrm{atTop}$ has the cluster points $-1$ and $1$, and no limit. For example, each neighbourhood of $1$ contains $u_n$ for each large even $n$, so it meets each tail of the sequence. A point $y \notin \{-1, 1\}$ has a neighbourhood that contains $u_n$ for finitely many $n$ only, and this neighbourhood misses a tail.

**Counterexample (Sequences are not enough).** Let $X = \mathbb{R}$ with the cocountable topology: the open sets are $\emptyset$ and the sets with a countable complement. The axioms hold, since a union of open sets has as complement an intersection of countable sets, and $X \setminus (U \cap V) = (X \setminus U) \cup (X \setminus V)$ is countable.

A sequence $(a_n)$ tends to $x$ only if it is eventually equal to $x$. Indeed, the set $C = \{a_n : a_n \ne x\}$ is countable, so $X \setminus C$ is an open neighbourhood of $x$, and $a_n \in X \setminus C$ means $a_n = x$. So each set is sequentially closed. But the set $A = \mathbb{R} \setminus \{0\}$ is not closed: its complement $\{0\}$ is not open. Its closure is $\mathbb{R}$, since each nonempty open set is uncountable and meets $A$. So $0 \in \overline{A}$, and no sequence in $A$ tends to $0$. The closure theorem gives a filter instead: $F = \mathcal{N}(0) \sqcap \mathcal{P}(A)$ is proper and tends to $0$.

The same space shows that the sequential criterion for continuity fails. The identity map from $X$ to $\mathbb{R}$ with its discrete topology preserves the limits of all sequences, since convergent sequences are eventually constant. It is not continuous, since $\{0\}$ is open in the discrete topology and not in $X$.

**Example (A principal ultrafilter).** The ultrafilter $\mathcal{P}(\{x\})$ tends to $x$ in each space, since each neighbourhood of $x$ contains $x$. In a Hausdorff space it tends to no other point. In the indiscrete space it tends to each point. A free ultrafilter on $\mathbb{N}$, that is, one with no finite member, exists by the ultrafilter lemma applied to the cofinite filter.

### The library around it

Cluster points are in `Mathlib.Topology.ClusterPt`, ultrafilters in `Mathlib.Order.Filter.Ultrafilter.Defs`, and their topological properties in `Mathlib.Topology.Ultrafilter`. Sequences are in `Mathlib.Topology.Sequences`, with the definitions in `Mathlib.Topology.Defs.Sequences`. Mathlib prefers the filter statements and proves the sequence forms only under a hypothesis such as `FrechetUrysohnSpace` or `FirstCountableTopology`.

A frequent pattern in Mathlib proofs: to prove a property of all limits of a filter, take an ultrafilter below it with `Ultrafilter.of`, use `Ultrafilter.em` or `mem_or_compl_mem` to make a decision, and pass to a limit with `Ultrafilter.clusterPt_iff`. Chapter 5 uses this pattern for the Tychonoff theorem.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that $x$ is a cluster point of a sequence $u$ along $\mathrm{atTop}$ if and only if each neighbourhood of $x$ contains $u_n$ for infinitely many $n$.
2. (A) Show that if $G \le F$ and $x$ is a cluster point of $G$, then $x$ is a cluster point of $F$.
3. (A) Show that an ultrafilter on a finite set is principal.
4. (B) In a first countable space, show that $x$ is a cluster point of a sequence if and only if some subsequence tends to $x$.
5. (B) Show that an ultrafilter $U$ that contains a finite set $A$ is principal: $U = \mathcal{P}(\{a\})$ for some $a \in A$.
6. (B) Show that a filter $F$ is the intersection, as families of sets, of the ultrafilters $U \le F$.
7. (B) Show that the cocountable topology on $\mathbb{R}$ is not first countable.
8. (C) Let $U$ be a free ultrafilter on $\mathbb{N}$. Show that each bounded real sequence $u$ has exactly one limit along $U$, that is, $u_{*}U \le \mathcal{N}(L)$ for exactly one $L$. Show that $u \mapsto L$ is linear and multiplicative.

### Notes and history

Ultrafilters appear in Cartan's notes of 1937, and Bourbaki uses them to prove the Tychonoff theorem. The ultrafilter lemma is weaker than the axiom of choice, but it does not follow from the axioms of Zermelo-Fraenkel set theory alone. The cocountable example of the failure of sequences is classical; Steen and Seebach, *Counterexamples in topology*, list the cocountable topology among their examples. The limit along a free ultrafilter of Exercise 8 is the Banach limit construction in one form and the base of nonstandard analysis.

### Reference

<?reference?>
