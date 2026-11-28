---
title: The lemma of Urysohn
kind: theory
modules:
  - Mathlib.Topology.UrysohnsLemma
  - Mathlib.Topology.Separation.CompletelyRegular
  - Mathlib.Topology.UrysohnsBounded
explains:
  E3: [exists_continuous_zero_one_of_isClosed]
  E2: [exists_continuous_zero_one_of_isCompact, Urysohns.CU, Urysohns.CU.lim, Urysohns.CU.continuous_lim, Urysohns.CU.lim_eq_midpoint, NormalSpace.instCompletelyRegularSpace, T4Space.instT35Space]
  E1: auto
families: []
requires: [V13.C01, V13.C03, V13.C04, V13.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The lemma of Urysohn

### Overview

In a metric space, two disjoint closed sets $A$ and $B$ are separated by the function $f(x) = d(x, A) / (d(x, A) + d(x, B))$. It is continuous, $0$ on $A$ and $1$ on $B$. A normal space has no distance, but the lemma of Urysohn says that such a function still exists. The proof builds the level sets of $f$ one dyadic rational at a time, using normality at each step. This section proves the lemma and gives its first consequences: the completely regular spaces and the compact Hausdorff case.

### Definitions

**Definition (Completely regular).** A space $X$ is completely regular if for each closed set $C$ and each point $x \notin C$ there is a continuous $f : X \to [0, 1]$ with $f(x) = 0$ and $f = 1$ on $C$. A completely regular $T_0$ space is called a $T_{3\frac12}$ space, or a Tychonoff space.

A completely regular space is regular: the sets $\{f < 1/2\}$ and $\{f > 1/2\}$ are disjoint open neighbourhoods of $x$ and $C$.

Chapter 4 introduced the class `CompletelyRegularSpace` for this definition. This chapter proves that normal spaces belong to it.

### Theorems and proofs

The proof uses one form of normality from Chapter 4: if $C$ is closed, $U$ is open and $C \subseteq U$, there is an open $V$ with $C \subseteq V \subseteq \overline{V} \subseteq U$. To get it, apply normality to the disjoint closed sets $C$ and $X \setminus U$. This gives disjoint open sets $V \supseteq C$ and $W \supseteq X \setminus U$. Then $\overline{V} \subseteq X \setminus W \subseteq U$, since $X \setminus W$ is closed and contains $V$.

**Theorem (Urysohn).** Let $X$ be normal and $A, B$ disjoint closed sets. There is a continuous $f : X \to [0, 1]$ with $f = 0$ on $A$ and $f = 1$ on $B$.

*Proof.* Let $D$ be the set of dyadic rationals in $[0, 1]$, the numbers $k / 2^n$. Step 1 constructs open sets $U_r$ for $r \in D$ such that:

- $A \subseteq U_0$ and $U_1 = X \setminus B$;
- $\overline{U_r} \subseteq U_s$ for $r < s$ in $D$.

Set $U_1 = X \setminus B$, an open set that contains $A$. By normality choose an open $U_0$ with $A \subseteq U_0 \subseteq \overline{U_0} \subseteq U_1$. Suppose $U_r$ is defined for all $r$ with denominator $2^n$ and satisfies the condition. Let $r = (2k + 1)/2^{n+1}$, with neighbours $a = k / 2^n$ and $b = (k + 1)/2^n$. Then $\overline{U_a} \subseteq U_b$, so by normality there is an open $U_r$ with $\overline{U_a} \subseteq U_r \subseteq \overline{U_r} \subseteq U_b$. The condition holds for all pairs with denominator $2^{n+1}$, since each new set fits between its two neighbours. By induction, $U_r$ is defined for all $r \in D$.

Step 2 defines $f$. Set $U_r = X$ for $r > 1$ in the dyadic rationals. Let

$$f(x) = \inf \{ r \in D \cup (1, 2] : x \in U_r \}.$$

Then $0 \le f(x) \le 1$. On $A \subseteq U_0$ the value is $0$. On $B$, no $U_r$ with $r \le 1$ contains $x$, since $U_r \subseteq U_1 = X \setminus B$, so the value is $1$.

Step 3 gives two facts. First, if $x \in \overline{U_r}$, then $f(x) \le r$: for each dyadic $s > r$, $x \in \overline{U_r} \subseteq U_s$, and the dyadics are dense. Second, if $x \notin U_r$, then $f(x) \ge r$: for $s < r$, $U_s \subseteq \overline{U_s} \subseteq U_r$, so $x \notin U_s$.

Step 4 proves continuity. It suffices to show that $\{f < c\}$ and $\{f > c\}$ are open for each real $c$, since these sets generate the topology of $\mathbb{R}$. If $f(x) < c$, there is a dyadic $r < c$ with $x \in U_r$, by the definition of the infimum. Conversely, if $x \in U_r$ with $r < c$, then $f(x) \le r < c$. So $\{f < c\} = \bigcup_{r < c} U_r$, which is open. If $f(x) > c$, choose a dyadic $r$ with $c < r < f(x)$. By the first fact of Step 3, $x \notin \overline{U_r}$. Conversely, if $x \notin \overline{U_r}$ for some $r > c$, then $x \notin U_r$, and $f(x) \ge r > c$ by the second fact. So $\{f > c\} = \bigcup_{r > c} (X \setminus \overline{U_r})$, which is open. $\square$

::: mathlib
`exists_continuous_zero_one_of_isClosed` · `Mathlib.Topology.UrysohnsLemma`

The theorem in a `NormalSpace`. The function is a `C(X, ℝ)` with `Set.EqOn f 0 s`, `Set.EqOn f 1 t` and values in `Icc 0 1`.

<?decl exists_continuous_zero_one_of_isClosed?>
:::

::: mathlib
`Urysohns.CU` · `Mathlib.Topology.UrysohnsLemma`

The proof in Mathlib avoids the choice of all the $U_r$ at once. A `CU P` is a pair of a closed set `C` and an open set `U` with `C ⊆ U`. Each such pair is split into a left pair `(C, V)` and a right pair `(closure V, U)`. The function `Urysohns.CU.lim` is defined by recursion on the depth, and `Urysohns.CU.lim_eq_midpoint` says that its value is the midpoint of the values for the two halves. Continuity is `Urysohns.CU.continuous_lim`. The parameter `P` lets one proof cover both normal spaces and the locally compact case below.

<?decl Urysohns.CU?>
:::

**Corollary (Normal implies completely regular).** Each normal $T_1$ space is completely regular. In particular each compact Hausdorff space and each metric space is completely regular.

*Proof.* In a $T_1$ space, $\{x\}$ is closed. Apply the theorem to $\{x\}$ and a closed set $C$ with $x \notin C$. Compact Hausdorff spaces and metric spaces are normal by Chapter 5 and Chapter 4. $\square$

::: mathlib
`NormalSpace.instCompletelyRegularSpace` · `Mathlib.Topology.Separation.CompletelyRegular`

The corollary as an instance: a normal space with `R0Space` is completely regular. Mathlib states it with the weaker axiom `R0Space`, which says that the closure of a point is inside each of its open neighbourhoods. `T4Space.instT35Space` is the version with $T_1$.

<?decl NormalSpace.instCompletelyRegularSpace?>
:::

**Corollary (Locally compact version).** Let $X$ be locally compact and Hausdorff, $K$ compact, $F$ closed and $K \cap F = \emptyset$. There is a continuous $f : X \to [0, 1]$ with $f = 0$ on $K$ and $f = 1$ on $F$.

*Proof sketch.* The space need not be normal, but Step 1 only needs the interpolation property for a compact $C$ inside an open $U$. In a locally compact Hausdorff space there is an open $V$ with compact closure and $C \subseteq V \subseteq \overline{V} \subseteq U$. So all closed sets of Step 1 can be chosen compact, and the rest of the proof is unchanged. $\square$

::: mathlib
`exists_continuous_zero_one_of_isCompact` · `Mathlib.Topology.UrysohnsLemma`

The corollary, in a regular locally compact space. It is the starting point of the Riesz representation theorem in the volume on measure theory.

<?decl exists_continuous_zero_one_of_isCompact?>
:::

### Examples

**Example (Metric spaces).** In a metric space the function $f(x) = d(x, A) / (d(x, A) + d(x, B))$ proves the theorem directly. The denominator is positive, since a point at distance $0$ from both closed sets lies in both. The lemma of Urysohn is needed only when no metric is available, for example in uncountable products of $[0, 1]$.

**Example (Embedding in a cube).** Let $X$ be completely regular and $T_1$, and let $\mathcal{F}$ be the set of continuous maps $X \to [0, 1]$. The map $e : X \to [0, 1]^{\mathcal{F}}$, $e(x)_f = f(x)$, is continuous and injective. It is a homeomorphism onto its image, since for $x \notin C$ a function $f$ with $f(x) = 0$ and $f = 1$ on $C$ gives the open set $\{y : y_f < 1/2\}$. The cube is compact by the Tychonoff theorem. So each $T_{3\frac12}$ space is a subspace of a compact Hausdorff space. The closure of the image is the Stone-Čech compactification.

**Counterexample (Regular but not completely regular).** There are regular $T_1$ spaces on which each continuous real function is constant. The first example is due to Hewitt (1946). So the lemma of Urysohn needs more than regularity, and normality is the standard hypothesis.

### The library around it

The lemma and its locally compact version are in `Mathlib.Topology.UrysohnsLemma`. Completely regular spaces and their embedding into the Stone-Čech compactification are in `Mathlib.Topology.Separation.CompletelyRegular`. The normality of metric spaces and compact Hausdorff spaces, which the corollary uses, is in the files of Chapter 4 and Chapter 5.

The module `Mathlib.Topology.UrysohnsBounded` restates the lemma with bounded continuous functions, the form that the proof of the theorem of Tietze uses. In a normal space, `exists_bounded_zero_one_of_closed` gives a bounded continuous $f : X \to \mathbb{R}$ with $f = 0$ on $s$, $f = 1$ on $t$ and $0 \le f \le 1$. The lemma `exists_bounded_mem_Icc_of_closed_of_le` gives the same with any two values $a \le b$ in place of $0$ and $1$.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that a subspace of a completely regular space is completely regular.
2. (A) Show that the function in the metric example is continuous, $0$ on $A$ and $1$ on $B$.
3. (A) Show that in the lemma of Urysohn one can ask for $f = 0$ exactly on $A$ when $A$ is a $G_\delta$ set. Hint: sum functions $2^{-n} f_n$.
4. (B) Show that a $T_1$ space is normal if and only if each two disjoint closed sets are separated by a continuous real function.
5. (B) Show that a connected normal $T_1$ space with at least two points is uncountable.
6. (C) Show that a compact Hausdorff space $X$ is metrizable if it is second countable. Hint: use countably many Urysohn functions to embed $X$ in $[0, 1]^{\mathbb{N}}$.

### Notes and history

Urysohn proved the lemma in 1925, in a paper on the cardinality of connected spaces that appeared after his death in 1924. He used it to prove his metrization theorem: each second countable regular $T_1$ space is metrizable. Tychonoff introduced completely regular spaces in 1930 and proved that they are exactly the subspaces of cubes.

### Reference

<?reference?>
