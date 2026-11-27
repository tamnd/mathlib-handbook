---
title: Minimal and topologically transitive actions
kind: theory
modules:
  - Mathlib.Dynamics.Minimal
  - Mathlib.Dynamics.Transitive
explains:
  E3: [MulAction.IsMinimal, isMinimal_iff_isClosed_smul_invariant, dense_of_nonempty_smul_invariant, MulAction.IsTopologicallyTransitive, MulAction.isTopologicallyTransitive_of_isMinimal, MulAction.isTopologicallyTransitive_iff_dense_iUnion]
  E2: [MulAction.dense_orbit, denseRange_smul, IsOpen.exists_smul_mem, IsOpen.iUnion_preimage_smul, IsOpen.iUnion_smul, IsCompact.exists_finite_cover_smul, MulAction.isMinimal_of_pretransitive, MulAction.isTopologicallyTransitive_iff, MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage, MulAction.isTopologicallyTransitive_iff_dense_of_preimage_invariant, IsOpen.dense_iUnion_preimage_smul, IsOpen.dense_of_preimage_smul_invariant, AddAction.IsMinimal, AddAction.IsTopologicallyTransitive]
  E1: auto
families: []
requires: [V04, V05, V13, V21.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Minimal and topologically transitive actions

### Overview

A system is minimal when it has no proper closed invariant piece: every orbit is dense. It is topologically transitive when any two open sets are joined by the action. Minimality is a topological form of irreducibility; transitivity says that the action carries every region into every other. This section works with an action of a monoid $M$ on a topological space $X$, as in Volume 5, Chapter 6, which covers the flows of Chapter 2 and the actions of groups. It proves that minimality means the absence of closed invariant sets, that minimal sets exist on compact spaces, that minimal actions are transitive, that transitive actions on Baire spaces have dense orbits, and that irrational rotations are minimal.

### Definitions

**Definition (Minimal action).** An action of a monoid $M$ on a topological space $X$ is *minimal* if the orbit $M \cdot x = \{c \cdot x : c \in M\}$ is dense in $X$ for every $x \in X$.

**Definition (Minimal set).** For an action by continuous maps, a *minimal set* is a nonempty closed set $K$ with $c \cdot K \subseteq K$ for all $c$, such that the restricted action on $K$ is minimal.

**Definition (Topologically transitive action).** The action is *topologically transitive* if for all nonempty open sets $U$ and $V$ there is $c \in M$ with $(c \cdot U) \cap V \neq \emptyset$.

::: mathlib
`MulAction.IsMinimal` · `Mathlib.Dynamics.Minimal`

`MulAction.IsMinimal M α` is a class with one field, `dense_orbit : ∀ x, Dense (orbit M x)`, for `[Monoid M] [TopologicalSpace α] [MulAction M α]`. `AddAction.IsMinimal` is the additive form, used for flows and rotations. `denseRange_smul` restates the field as `DenseRange fun c ↦ c • x`. A transitive action in the algebraic sense is minimal: `MulAction.isMinimal_of_pretransitive`.

<?decl MulAction.IsMinimal?>
:::

::: mathlib
`MulAction.IsTopologicallyTransitive` · `Mathlib.Dynamics.Transitive`

A class with the field `exists_smul_inter : IsOpen U → U.Nonempty → IsOpen V → V.Nonempty → ∃ m, (m • U ∩ V).Nonempty`, and `MulAction.isTopologicallyTransitive_iff` unfolds it. Here `m • U` is the image of `U`. The additive form is `AddAction.IsTopologicallyTransitive`.

<?decl MulAction.IsTopologicallyTransitive?>
:::

### Theorems and proofs

**Theorem (Minimality and closed invariant sets).** Suppose each map $x \mapsto c \cdot x$ is continuous. The action is minimal if and only if the only closed sets $S$ with $c \cdot S \subseteq S$ for all $c$ are $\emptyset$ and $X$. In a minimal action, every nonempty invariant set is dense, and every nonempty open set $U$ satisfies $\bigcup_c \{x : c \cdot x \in U\} = X$.

*Proof.* Suppose the action is minimal and $S$ is closed, invariant and nonempty. Take $x \in S$. The orbit of $x$ lies in $S$, so $X = \overline{M \cdot x} \subseteq S$. Conversely, suppose the condition and let $x \in X$. The orbit is invariant, since $c \cdot (c' \cdot x) = (cc') \cdot x$, and its closure is invariant because each $c$ acts continuously (Chapter 2, Section 1). It is nonempty and closed, so it is $X$. The second claim uses the same argument without the continuity: a nonempty invariant set contains an orbit, which is dense. For the third, the orbit of $x$ is dense and so meets $U$, which gives $c$ with $c \cdot x \in U$. $\square$

::: mathlib
`isMinimal_iff_isClosed_smul_invariant` · `Mathlib.Dynamics.Minimal`

`[ContinuousConstSMul M α] → (IsMinimal M α ↔ ∀ s, IsClosed s → (∀ c, c • s ⊆ s) → s = ∅ ∨ s = univ)`. The second claim is `dense_of_nonempty_smul_invariant`, and the third is `IsOpen.iUnion_preimage_smul`, with `IsOpen.exists_smul_mem` for a single point. For a group, `IsOpen.iUnion_smul` says `⋃ g, g • U = univ`.

<?decl isMinimal_iff_isClosed_smul_invariant?>
:::

**Corollary (Finite covers).** Let a group $G$ act minimally by homeomorphisms, $K$ compact and $U$ open and nonempty. Then finitely many translates $g_1 U, \ldots, g_k U$ cover $K$.

*Proof.* The open sets $gU$ cover $X$ by the theorem, so finitely many cover $K$. $\square$

This is `IsCompact.exists_finite_cover_smul`.

**Theorem (Existence of minimal sets).** Let $X$ be a nonempty compact space with an action of $M$ by continuous maps. Then $X$ contains a minimal set.

*Proof.* Let $\mathcal{F}$ be the family of nonempty closed sets $S$ with $c \cdot S \subseteq S$ for all $c$, ordered by inclusion. It contains $X$. Let $\mathcal{C} \subseteq \mathcal{F}$ be a nonempty chain and $S_\infty = \bigcap \mathcal{C}$. It is closed and invariant. Any finite subfamily of the chain has a smallest member, so the intersection of the finite subfamily is nonempty; by compactness $S_\infty \neq \emptyset$. So every chain has a lower bound in $\mathcal{F}$, and Zorn's lemma of Volume 4 gives a member $K$ that is minimal for inclusion. By the theorem above applied to the action on $K$ (the closed invariant subsets of $K$ are closed invariant subsets of $X$), the action on $K$ is minimal. $\square$

The index of this edition has no declaration for the existence of minimal sets. The two ingredients are `zorn_superset_nonempty` and `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`.

<?decl zorn_superset_nonempty?>

**Theorem (Minimal implies transitive).** A minimal action is topologically transitive. A set $U$ satisfies the condition of transitivity if and only if $\bigcup_c c \cdot U$ is dense, so the action is transitive if and only if $\bigcup_c c \cdot U$ is dense for every nonempty open $U$.

*Proof.* Let $U$ and $V$ be nonempty open and $x \in U$. The orbit of $x$ is dense, so some $c \cdot x$ lies in $V$, and $c \cdot x \in (c \cdot U) \cap V$. For the second claim, $\bigcup_c c \cdot U$ meets every nonempty open $V$ exactly when some $c \cdot U$ meets $V$, and a set is dense exactly when it meets every nonempty open set. $\square$

::: mathlib
`MulAction.isTopologicallyTransitive_of_isMinimal` · `Mathlib.Dynamics.Transitive`

An instance: `[IsMinimal M α] → IsTopologicallyTransitive M α`. The density forms are `isTopologicallyTransitive_iff_dense_iUnion` and, with preimages, `isTopologicallyTransitive_iff_dense_iUnion_preimage`. With `[ContinuousConstSMul M α]`, `isTopologicallyTransitive_iff_dense_of_preimage_invariant` says that the action is transitive if and only if every nonempty open $U$ with $c^{-1}(U) \subseteq U$ for all $c$ is dense.

<?decl MulAction.isTopologicallyTransitive_of_isMinimal?>
:::

**Theorem (Dense orbits).** Let $X$ be a Baire space with a countable base, and $M$ act transitively by continuous maps. Then the set of points with dense orbit is a dense $G_\delta$, in particular nonempty.

*Proof.* Let $(V_k)$ be a countable base of nonempty open sets. Put $W_k = \bigcup_c \{x : c \cdot x \in V_k\}$, open since each $c$ acts continuously. For a nonempty open $U$, transitivity gives $c$ and $u \in U$ with $c \cdot u \in V_k$, so $u \in U \cap W_k$; thus $W_k$ is dense. By the Baire theorem of Volume 13, Chapter 3, $\bigcap_k W_k$ is dense. A point $x$ lies in it exactly when its orbit meets every $V_k$, that is, when its orbit is dense. $\square$

### Examples

**Example (Irrational rotation).** Let $\alpha$ be irrational and $R(x) = x + \alpha$ on $\mathbb{T} = \mathbb{R}/\mathbb{Z}$. The forward orbit $\{x + n\alpha : n \ge 0\}$ of every $x$ is dense, so the action of $\mathbb{N}$ is minimal. Proof: Let $\varepsilon > 0$ and $N > 1/\varepsilon$. Of the $N + 1$ points $k\alpha$, $0 \le k \le N$, two lie in an arc of length $1/N$, say $j\alpha$ and $k\alpha$ with $j < k$. Put $q = k - j$. Then $q\alpha$ is at distance $\delta < \varepsilon$ from $0$ in $\mathbb{T}$, and $\delta > 0$ because $q\alpha \notin \mathbb{Z}$. The points $x + mq\alpha$, $m \ge 0$, move around the circle in steps of length $\delta$ in one direction, so they meet every arc of length $\varepsilon$. For a rational $\alpha = p/q$, every orbit is finite, and the rotation is not minimal.

::: mathlib
`AddCircle.denseRange_zsmul_coe_iff` · `Mathlib.Topology.Instances.AddCircle.DenseSubgroup`

`(DenseRange fun n : ℤ ↦ n • (a : AddCircle p)) ↔ Irrational (a / p)`: the orbit of $0$ under the rotation by $a$, as an action of $\mathbb{Z}$, is dense exactly for an irrational ratio.

<?decl AddCircle.denseRange_zsmul_coe_iff?>
:::

**Example (Transitive, not minimal).** The doubling map $D(x) = 2x$ on $\mathbb{T}$, as an action of $\mathbb{N}$, is transitive: a nonempty open set contains a closed arc of length $2^{-n}$ for some $n$, and $D^{[n]}$ maps it onto $\mathbb{T}$. It is not minimal, since $0$ is fixed and $\{0\}$ is a closed invariant set. By the theorem on dense orbits, some point has a dense forward orbit; in binary, a point whose expansion lists all finite words is one.

### The library around it

The definitions work for any monoid action, with no topology on $M$. A `Flow` of Chapter 2 gives an action by `Flow.toAddAction`, so both notions apply to flows. Chapter 6 uses minimality to prove ergodicity of group actions, and Chapter 7 uses the shift spaces of Section 2, which are transitive and contain many minimal sets.

Common errors of a learner:

- Minimality is a class on the pair `M α`. For a single map `f`, one needs an action of `ℕ` or `ℤ` first, such as `Flow.toAddAction` of `Flow.fromIter`.
- `m • U` in the definition of transitivity is the image; for a noninvertible map the preimage form is a different statement, related by `isTopologicallyTransitive_iff_dense_iUnion_preimage`.

### Exercises

1. (A) Show that the identity action of the trivial monoid on $X$ is minimal if and only if $X$ has the indiscrete topology or at most one point.
2. (A) Show that a minimal action of $\mathbb{N}$ by a continuous map on an infinite Hausdorff space has no periodic point. Hint: a finite orbit is closed and invariant.
3. (B) Show that every orbit closure of a rational rotation is a minimal set. Find two distinct minimal sets of the doubling map, and show that the orbit closure of a point with dense orbit is not minimal.
4. (B) Let $\pi$ be a semiconjugacy of $\mathbb{N}$-flows in the sense of Chapter 2. Show that a factor of a minimal flow is minimal, and that a factor of a transitive flow is transitive.
5. (B) Show that the translation $x \mapsto x + 1$ on $\mathbb{R}$ has no minimal set, and find the hypothesis of the existence theorem that fails.
6. (C) Let $\alpha$ be irrational. Show that the flow $\phi_t(x, y) = (x + t, y + t\alpha)$ on $\mathbb{R}^2/\mathbb{Z}^2$ is minimal. Hint: the orbit returns to the circle $\{0\} \times \mathbb{T}$ at integer times, along the orbit of the rotation by $\alpha$.

### Notes and history

Minimal sets were introduced by Birkhoff, who proved their existence on compact spaces and studied the recurrence of their points. The density of the orbits of an irrational rotation is often attributed to Kronecker, whose theorem treats several rotations at once.

### Reference

<?reference?>
