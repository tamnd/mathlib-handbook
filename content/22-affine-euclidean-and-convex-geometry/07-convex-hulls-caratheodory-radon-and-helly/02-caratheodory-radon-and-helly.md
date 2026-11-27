---
title: The theorems of Caratheodory, Radon and Helly
kind: theory
modules:
  - Mathlib.Analysis.Convex.Caratheodory
  - Mathlib.Analysis.Convex.Radon
explains:
  E3: [Caratheodory.mem_convexHull_erase, convexHull_eq_union, Convex.radon_partition, Convex.helly_theorem, Convex.helly_theorem_compact]
  E2: ["Convex.helly_theorem'"]
  E1: auto
families: []
requires: [V07, V13, V16.C05, V22.C02, V22.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The theorems of Caratheodory, Radon and Helly

### Overview

Section 1 describes the convex hull of $A$ as the set of finite convex combinations of points of $A$. The theorem of Caratheodory says that in dimension $d$ such a combination needs at most $d + 1$ points. An affine relation among the points lets one weight drop to zero. The same relation splits $d + 2$ points into two groups whose hulls meet, which is the theorem of Radon. From Radon follows the theorem of Helly: if every $d + 1$ members of a finite family of convex sets in dimension $d$ meet, then all of them meet.

### Definitions

Let $E$ be a vector space of dimension $d$ over an ordered field $K$.

**Definition (affine relation).** An *affine relation* among points $p_1, \dots, p_n$ of $E$ is a family $g_1, \dots, g_n \in K$, not all zero, with $\sum_i g_i = 0$ and $\sum_i g_i p_i = 0$. The points are *affinely dependent* if they admit one. By Chapter 2, an affinely independent family in $E$ has at most $d + 1$ members.

**Definition (Radon partition).** A *Radon partition* of a family $(p_i)_{i \in I}$ is a set $J \subseteq I$ with $\mathrm{conv}\{p_j : j \in J\} \cap \mathrm{conv}\{p_j : j \notin J\} \ne \emptyset$.

### Theorems and proofs

**Lemma (dropping a point).** Let $T \subseteq E$ be finite and affinely dependent, and let $x \in \mathrm{conv}(T)$. Then $x \in \mathrm{conv}(T \setminus \{t_0\})$ for some $t_0 \in T$.

*Proof.* Write $x = \sum_{t \in T} f_t\, t$ with $f_t \ge 0$ and $\sum f_t = 1$. Let $(g_t)$ be an affine relation on $T$. The $g_t$ sum to $0$ and are not all $0$, so some $g_t$ is positive. Let
$$\lambda = \min \Big\{ \frac{f_t}{g_t} : g_t > 0 \Big\},$$
attained at $t_0$. Put $k_t = f_t - \lambda g_t$. Then $\sum k_t = 1 - \lambda \cdot 0 = 1$ and $\sum k_t\, t = x - \lambda \cdot 0 = x$. If $g_t \le 0$, then $k_t \ge f_t \ge 0$. If $g_t > 0$, then $f_t / g_t \ge \lambda$, so $k_t \ge 0$. Finally $k_{t_0} = 0$. So $x$ is a convex combination of the points of $T \setminus \{t_0\}$. $\square$

**Theorem (Caratheodory).** Let $A \subseteq E$ and $x \in \mathrm{conv}(A)$. Then there is an affinely independent finite set $T \subseteq A$ with $x \in \mathrm{conv}(T)$. In particular $x$ is a convex combination of at most $d + 1$ points of $A$, and
$$\mathrm{conv}(A) = \bigcup \{ \mathrm{conv}(T) : T \subseteq A \text{ finite and affinely independent} \}.$$

*Proof.* By Section 1, $x \in \mathrm{conv}(T)$ for some finite $T \subseteq A$. Choose such a $T$ with the least number of points. If $T$ were affinely dependent, the lemma would give a smaller set $T \setminus \{t_0\}$ with $x$ in its hull. So $T$ is affinely independent, and it has at most $d + 1$ points. The displayed equality follows by monotonicity of the hull. $\square$

A consequence: for compact $C \subseteq \mathbb{R}^d$, $\mathrm{conv}(C)$ is the image of the compact set $C^{d+1} \times \Delta_d$ under $(p, w) \mapsto \sum_i w_i p_i$, so it is compact.

**Theorem (Radon).** Let $(p_i)_{i \in I}$ be an affinely dependent family in $E$. Then it has a Radon partition. In particular, any $d + 2$ points of $E$, with repetitions allowed, have a Radon partition.

*Proof.* Take an affine relation $(g_i)$, supported on a finite set of indices. Let $J = \{ i : g_i > 0 \}$. Since $\sum g_i = 0$ and not all $g_i$ are $0$, the set $J$ is not empty, and $S = \sum_{i \in J} g_i > 0$ equals $\sum_{i \notin J} (-g_i)$. The relation $\sum_i g_i p_i = 0$ gives
$$z := \sum_{i \in J} \frac{g_i}{S}\, p_i = \sum_{i \notin J} \frac{-g_i}{S}\, p_i.$$
On each side the weights are nonnegative and sum to $1$, so $z$ lies in both hulls. A repeated point $p_i = p_j$ gives the relation $g_i = 1$, $g_j = -1$, and $d + 2$ distinct points are dependent by Chapter 2. $\square$

**Theorem (Helly).** Let $F_1, \dots, F_n$ be convex subsets of $E$ with $n \ge d + 1$. Suppose that each $d + 1$ of them have a common point. Then $F_1 \cap \dots \cap F_n \ne \emptyset$.

*Proof.* Induct on $n$. For $n = d + 1$ the hypothesis is the conclusion. Let $n \ge d + 2$. For each $j$, the $n - 1 \ge d + 1$ sets $F_i$ with $i \ne j$ satisfy the hypothesis, so by induction they have a common point $x_j$.

The family $(x_1, \dots, x_n)$ has $n \ge d + 2$ members, so Radon gives $J \subseteq \{1, \dots, n\}$ and a point
$$z \in \mathrm{conv}\{x_j : j \in J\} \cap \mathrm{conv}\{x_j : j \notin J\}.$$
Fix $i$. If $i \notin J$, then each $j \in J$ has $j \ne i$, so $x_j \in F_i$. Since $F_i$ is convex, $\mathrm{conv}\{x_j : j \in J\} \subseteq F_i$, so $z \in F_i$. If $i \in J$, then each $j \notin J$ has $j \ne i$, and the same argument with the other hull gives $z \in F_i$. So $z$ lies in every $F_i$. $\square$

**Corollary (Helly for compact families).** Let $(F_\alpha)_{\alpha \in A}$ be a family of at least $d + 1$ compact convex subsets of $E = \mathbb{R}^d$ such that each $d + 1$ of them have a common point. Then $\bigcap_\alpha F_\alpha \ne \emptyset$.

*Proof.* By Helly, each finite subfamily meets. So the closed sets $F_\alpha$ have the finite intersection property in the compact space $F_{\alpha_0}$, and their intersection is not empty (Volume 13). $\square$

### Examples

**Example (Caratheodory on a square).** Let $p_1 = (0,0)$, $p_2 = (2,2)$, $p_3 = (2,0)$, $p_4 = (0,2)$ and $x = (1,1) = \sum \tfrac14 p_i$. An affine relation is $g = (1, 1, -1, -1)$: indeed $p_1 + p_2 - p_3 - p_4 = 0$. The ratios $f_t / g_t$ for $g_t > 0$ are $\tfrac14$ and $\tfrac14$, so $\lambda = \tfrac14$ and $t_0 = p_1$. Then $k = f - \tfrac14 g = (0, 0, \tfrac12, \tfrac12)$, and indeed $x = \tfrac12 (2,0) + \tfrac12 (0,2)$.

**Example (Helly in the plane, step by step).** In $\mathbb{R}^2$, so $d + 1 = 3$, let
$$F_1 = \{u \ge 0\},\quad F_2 = \{v \ge 0\},\quad F_3 = \{u + v \le 1\},\quad F_4 = \{(u-1)^2 + (v-1)^2 \le 1\}.$$
Each triple meets. $F_2 \cap F_3 \cap F_4$ contains $x_1 = (0, 1)$, since $0 + 1 \le 1$ and its distance to $(1,1)$ is $1$. $F_1 \cap F_3 \cap F_4$ contains $x_2 = (1, 0)$ by symmetry. $F_1 \cap F_2 \cap F_4$ contains $x_3 = (1,1)$. $F_1 \cap F_2 \cap F_3$ contains $x_4 = (0,0)$. The proof applies Radon to the four points. The relation $x_3 + x_4 - x_1 - x_2 = 0$ gives $J = \{3, 4\}$, $S = 2$ and $z = \tfrac12 x_3 + \tfrac12 x_4 = (\tfrac12, \tfrac12)$, which is also $\tfrac12 x_1 + \tfrac12 x_2$. It lies in all four sets.

**Counterexample (three is needed in the plane).** The three lines $\{v = 0\}$, $\{u = 0\}$ and $\{u + v = 1\}$ are convex, and each two of them meet. The three have no common point.

**Counterexample (compactness is needed for infinite families).** In $\mathbb{R}$ the intervals $(0, 1/n)$ meet in finite subfamilies but $\bigcap_n (0, 1/n) = \emptyset$.

### The library around it

::: mathlib
`Caratheodory.mem_convexHull_erase` · `Mathlib.Analysis.Convex.Caratheodory`

For a `Finset` `t` whose points, as a family `Subtype.val`, are not affinely independent, and `x ∈ convexHull 𝕜 ↑t`, there is `y` with `x ∈ convexHull 𝕜 ↑(t.erase ↑y)`.

<?decl Caratheodory.mem_convexHull_erase?>
:::

::: mathlib
`convexHull_eq_union` · `Mathlib.Analysis.Convex.Caratheodory`

The theorem of Caratheodory: `convexHull 𝕜 s` is the union of `convexHull 𝕜 ↑t` over the finite sets `t ⊆ s` that are affinely independent. The bound $d + 1$ follows from `AffineIndependent.card_le_finrank_succ` of Chapter 2.

<?decl convexHull_eq_union?>
:::

The index has no declaration for the compactness of the hull of a compact set, only `Set.Finite.isCompact_convexHull` for finite sets.

::: mathlib
`Convex.radon_partition` · `Mathlib.Analysis.Convex.Radon`

For a family `f : ι → E` that is not affinely independent, there is `I : Set ι` with `(convexHull 𝕜 (f '' I) ∩ convexHull 𝕜 (f '' Iᶜ)).Nonempty`.

<?decl Convex.radon_partition?>
:::

::: mathlib
`Convex.helly_theorem` · `Mathlib.Analysis.Convex.Radon`

For `F : ι → Set E` and `s : Finset ι` with `finrank 𝕜 E + 1 ≤ s.card`, convex members, and a common point for each `I ⊆ s` with `I.card = finrank 𝕜 E + 1`, the conclusion is `(⋂ i ∈ s, F i).Nonempty`. `Convex.helly_theorem'` asks the hypothesis for all `I` with at most $d + 1$ members.

<?decl Convex.helly_theorem?>
:::

::: mathlib
`Convex.helly_theorem_compact` · `Mathlib.Analysis.Convex.Radon`

The form for any index type `ι` with `finrank + 1 ≤ ENat.card ι`, in a Hausdorff topological vector space, with compact convex members.

<?decl Convex.helly_theorem_compact?>
:::

### Exercises

1. (A) Write $(1, 1)$ as a convex combination of at most three of the points $(0,0)$, $(3,0)$, $(0,3)$, $(3,3)$, $(1,2)$, using the lemma.
2. (A) Find a Radon partition of the four points $(0,0)$, $(4,0)$, $(0,4)$, $(1,1)$ and the common point of the two hulls.
3. (B) Show that the bound $d + 1$ in Caratheodory is sharp: find a point in the hull of the vertices of a $d$-simplex that is not in the hull of any $d$ of them. Hint: try the barycenter.
4. (B) Let $I_1, \dots, I_n$ be closed intervals in $\mathbb{R}$ such that any two meet. Show directly that all of them meet.
5. (C) Let $S \subseteq \mathbb{R}^2$ be finite. Show that if each three points of $S$ lie in a disc of radius $1$, then $S$ lies in a disc of radius $1$. Hint: apply Helly to the discs of radius $1$ centred at the points of $S$.
6. (C) Show that the hull of a compact set in an infinite-dimensional Hilbert space need not be closed. Hint: take the points $e_n / n$ and $0$ in $\ell^2$.

### Notes and history

Caratheodory proved his theorem in 1907 while he studied the coefficients of power series. Helly found his theorem in 1913. Radon published a proof in 1921 that uses the partition lemma now named after him, and Helly published his own proof in 1923. The Mathlib file on Caratheodory names Johan Commelin and Kim Morrison as authors. The file on Radon and Helly names Vasily Nesterov.

### Reference

<?reference?>
