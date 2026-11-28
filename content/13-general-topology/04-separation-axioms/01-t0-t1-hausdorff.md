---
title: The axioms T0, T1 and Hausdorff
kind: theory
modules:
  - Mathlib.Topology.Separation.Basic
  - Mathlib.Topology.Separation.Hausdorff
  - Mathlib.Topology.SeparatedMap
  - Mathlib.Topology.NatEmbedding
  - Mathlib.Topology.Separation.Connected
  - Mathlib.Topology.Separation.CountableSeparatingOn
  - Mathlib.Topology.Separation.DisjointCover
  - Mathlib.Topology.Separation.Lemmas
  - Mathlib.Topology.Separation.Profinite
  - Mathlib.Topology.SmallInductiveDimension
explains:
  E3: [T0Space, T1Space, T2Space]
  E2: [Inseparable, t0Space_iff_inseparable, T1Space.t1, isClosed_singleton, t1Space_iff_exists_open, T1Space.t0Space, instT1SpaceCofiniteTopology, t2_separation, t2Space_iff_disjoint_nhds, disjoint_nhds_nhds, T2Space.t1Space, tendsto_nhds_unique, Filter.Tendsto.limUnder_eq, t2_iff_isClosed_diagonal, isClosed_diagonal, T2Space.of_injective_continuous, instT2SpaceSubtype, Prod.t2Space, Pi.t2Space]
  E1: auto
families: []
requires: [V01, V13.C01, V13.C02, V13.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The axioms T0, T1 and Hausdorff

### Overview

Two points of a space are topologically indistinguishable if they have the same neighbourhoods. The axiom $T_0$ forbids this. The axiom $T_1$ asks that each point has a neighbourhood that misses a given other point, which is the same as asking that points are closed. The Hausdorff axiom $T_2$ asks that two distinct points have disjoint neighbourhoods.

The Hausdorff axiom is the one that analysis needs: it makes limits unique. In filter language it says that the neighbourhood filters of distinct points are disjoint, and the proof of uniqueness of limits is then one line. Mathlib uses it to define the function `limUnder` that returns the limit of a convergent map.

### Definitions

**Definition (Indistinguishable points, $T_0$, $T_1$, $T_2$).** Let $X$ be a topological space.

- Two points $x, y$ are inseparable if $\mathcal{N}(x) = \mathcal{N}(y)$.
- $X$ is $T_0$ if inseparable points are equal.
- $X$ is $T_1$ if for all $x \ne y$ there is an open $U$ with $x \in U$ and $y \notin U$.
- $X$ is $T_2$, or Hausdorff, if for all $x \ne y$ there are disjoint open sets $U \ni x$ and $V \ni y$.

*Remarks.* Each $T_2$ space is $T_1$, and each $T_1$ space is $T_0$. For $T_0$, two distinct points must differ in one open set, in one direction or the other: $x, y$ are inseparable if and only if each open set contains both or neither.

::: mathlib
`Inseparable` · `Mathlib.Topology.Defs.Filter`

`Inseparable x y` is `𝓝 x = 𝓝 y`. It is an equivalence relation, and the quotient by it is the Kolmogorov quotient `SeparationQuotient X`, which is $T_0$.

<?decl Inseparable?>
:::

::: mathlib
`T0Space` · `Mathlib.Topology.Separation.Basic`

The class says that `Inseparable` is the equality: `t0Space_iff_inseparable`. In Mathlib it is stated as the injectivity of `x ↦ 𝓝 x`.

<?decl T0Space?>
:::

::: mathlib
`t0Space_iff_inseparable` · `Mathlib.Topology.Separation.Basic`

$T_0$ means that inseparable points are equal.

<?decl t0Space_iff_inseparable?>
:::

::: mathlib
`T1Space` · `Mathlib.Topology.Separation.Basic`

The class has the field `t1 : ∀ x, IsClosed {x}`, the form of the theorem below. The form of the text is `t1Space_iff_exists_open`.

<?decl T1Space?>
:::

::: mathlib
`T1Space.t1` · `Mathlib.Topology.Separation.Basic`

The field of the class: singletons are closed.

<?decl T1Space.t1?>
:::

::: mathlib
`t1Space_iff_exists_open` · `Mathlib.Topology.Separation.Basic`

The definition of the text as an equivalence.

<?decl t1Space_iff_exists_open?>
:::

::: mathlib
`T2Space` · `Mathlib.Topology.Separation.Hausdorff`

The class has the field `t2`, the statement of the text with `Disjoint u v` for the disjointness. The lemma `t2_separation` extracts the two open sets.

<?decl T2Space?>
:::

::: mathlib
`t2_separation` · `Mathlib.Topology.Separation.Hausdorff`

Two distinct points have disjoint open neighbourhoods.

<?decl t2_separation?>
:::

### Theorems and proofs

**Theorem ($T_1$ and closed points).** A space $X$ is $T_1$ if and only if each singleton $\{x\}$ is closed. In a $T_1$ space each finite set is closed.

*Proof.* Assume $T_1$ and fix $x$. For each $y \ne x$ there is an open $U_y$ with $y \in U_y$ and $x \notin U_y$. The union $\bigcup_{y \ne x} U_y$ is open and equals $X \setminus \{x\}$. So $\{x\}$ is closed. Conversely, if $\{y\}$ is closed and $x \ne y$, then $U = X \setminus \{y\}$ is open, contains $x$, and misses $y$. A finite set is a finite union of closed singletons. $\square$

::: mathlib
`isClosed_singleton` · `Mathlib.Topology.Separation.Basic`

In a $T_1$ space, `{x}` is closed. The lemma `Set.Finite.isClosed` gives the closedness of finite sets.

<?decl isClosed_singleton?>
:::

::: mathlib
`T1Space.t0Space` · `Mathlib.Topology.Separation.Basic`

A $T_1$ space is $T_0$, as an instance.

<?decl T1Space.t0Space?>
:::

::: mathlib
`instT1SpaceCofiniteTopology` · `Mathlib.Topology.Separation.Basic`

The cofinite topology is $T_1$, since finite sets are closed. The example below shows that it is not $T_2$ on an infinite type.

<?decl instT1SpaceCofiniteTopology?>
:::

**Theorem (Hausdorff by filters).** A space $X$ is Hausdorff if and only if $\mathcal{N}(x) \sqcap \mathcal{N}(y) = \bot$ for all $x \ne y$.

*Proof.* The infimum $\mathcal{N}(x) \sqcap \mathcal{N}(y)$ has as members the sets $N \cap M$ with $N \in \mathcal{N}(x)$ and $M \in \mathcal{N}(y)$. It is $\bot$ if and only if it contains $\emptyset$, that is, if and only if $N \cap M = \emptyset$ for some neighbourhoods $N$ of $x$ and $M$ of $y$. These contain open sets $U \ni x$ and $V \ni y$, which are then disjoint. Conversely, disjoint open sets are disjoint neighbourhoods. $\square$

::: mathlib
`t2Space_iff_disjoint_nhds` · `Mathlib.Topology.Separation.Hausdorff`

The theorem. `Disjoint f g` for filters means `f ⊓ g = ⊥`, the disjointness in the lattice of filters. The lemma `disjoint_nhds_nhds` gives `Disjoint (𝓝 x) (𝓝 y) ↔ x ≠ y` in a Hausdorff space.

<?decl t2Space_iff_disjoint_nhds?>
:::

::: mathlib
`disjoint_nhds_nhds` · `Mathlib.Topology.Separation.Hausdorff`

In a Hausdorff space, the neighbourhood filters of two points are disjoint if and only if the points differ.

<?decl disjoint_nhds_nhds?>
:::

::: mathlib
`T2Space.t1Space` · `Mathlib.Topology.Separation.Hausdorff`

A Hausdorff space is $T_1$, as an instance.

<?decl T2Space.t1Space?>
:::

**Theorem (Uniqueness of limits).** Let $X$ be Hausdorff, $F$ a proper filter on a set $A$ and $f : A \to X$. If $f$ tends to $\mathcal{N}(a)$ and to $\mathcal{N}(b)$ along $F$, then $a = b$.

*Proof.* The two hypotheses say $f_{*}F \le \mathcal{N}(a)$ and $f_{*}F \le \mathcal{N}(b)$. So $f_{*}F \le \mathcal{N}(a) \sqcap \mathcal{N}(b)$. The filter $f_{*}F$ is proper, since $F$ is proper. If $a \ne b$, the right side is $\bot$, and so $f_{*}F = \bot$, a contradiction. $\square$

The proof covers the uniqueness of the limit of a sequence, of a function at a point, at infinity, and of each other kind at once.

::: mathlib
`tendsto_nhds_unique` · `Mathlib.Topology.Separation.Hausdorff`

The theorem. The hypothesis `[l.NeBot]` is necessary: along `⊥` each map tends to each point.

<?decl tendsto_nhds_unique?>
:::

::: mathlib
`Filter.Tendsto.limUnder_eq` · `Mathlib.Topology.Separation.Hausdorff`

The function `limUnder f u` chooses a limit of `u` along `f` when there is one, and an arbitrary point otherwise. In a Hausdorff space it returns the limit: from `Tendsto u f (𝓝 a)` this lemma gives `limUnder f u = a`. Mathlib proves most results with `Tendsto` and uses `limUnder` only when a function of the limit is needed.

<?decl Filter.Tendsto.limUnder_eq?>
:::

**Theorem (The diagonal).** A space $X$ is Hausdorff if and only if the diagonal $\Delta = \{(x, x) : x \in X\}$ is closed in $X \times X$.

*Proof.* The complement of $\Delta$ is the set of pairs $(x, y)$ with $x \ne y$. It is open if and only if each such pair has a basic neighbourhood $U \times V$ inside it, with $U \ni x$ and $V \ni y$ open. The condition $(U \times V) \cap \Delta = \emptyset$ means that no point lies in both $U$ and $V$, that is, $U \cap V = \emptyset$. $\square$

::: mathlib
`t2_iff_isClosed_diagonal` · `Mathlib.Topology.Separation.Hausdorff`

The theorem. The direction from `T2Space` is `isClosed_diagonal`.

<?decl t2_iff_isClosed_diagonal?>
:::

::: mathlib
`isClosed_diagonal` · `Mathlib.Topology.Separation.Hausdorff`

The diagonal of a Hausdorff space is closed.

<?decl isClosed_diagonal?>
:::

**Corollary (Agreement on a dense set).** Let $f, g : X \to Y$ be continuous and $Y$ Hausdorff. The set $\{x : f(x) = g(x)\}$ is closed. If $f = g$ on a dense set, then $f = g$.

*Proof.* The map $x \mapsto (f(x), g(x))$ is continuous into $Y \times Y$, and the set is the preimage of the closed diagonal. A closed set that contains a dense set is the whole space. $\square$

**Theorem (Stability).** A subspace of a Hausdorff space is Hausdorff. A product of Hausdorff spaces is Hausdorff. If $f : X \to Y$ is continuous and injective and $Y$ is Hausdorff, then $X$ is Hausdorff.

*Proof.* The last statement implies the first, for the inclusion. For it, let $x \ne x'$ in $X$. Then $f(x) \ne f(x')$, so there are disjoint open sets $V \ni f(x)$ and $V' \ni f(x')$. Their preimages are disjoint open sets around $x$ and $x'$. For a product, let $x \ne y$. Then $x_i \ne y_i$ for some $i$. Choose disjoint open $U \ni x_i$ and $V \ni y_i$ in $X_i$. Then $\pi_i^{-1}(U)$ and $\pi_i^{-1}(V)$ are disjoint open sets around $x$ and $y$. $\square$

::: mathlib
`T2Space.of_injective_continuous` · `Mathlib.Topology.Separation.Hausdorff`

The third statement of the theorem.

<?decl T2Space.of_injective_continuous?>
:::

::: mathlib
`instT2SpaceSubtype` · `Mathlib.Topology.Separation.Hausdorff`

A subtype of a Hausdorff space is Hausdorff.

<?decl instT2SpaceSubtype?>
:::

::: mathlib
`Prod.t2Space` · `Mathlib.Topology.Separation.Hausdorff`

A product of two Hausdorff spaces is Hausdorff.

<?decl Prod.t2Space?>
:::

::: mathlib
`Pi.t2Space` · `Mathlib.Topology.Separation.Hausdorff`

An arbitrary product of Hausdorff spaces is Hausdorff.

<?decl Pi.t2Space?>
:::

### Examples

**Example (Metric spaces are Hausdorff).** Let $x \ne y$ in a metric space and $r = d(x, y)/2 > 0$. If $z \in B(x, r) \cap B(y, r)$, then $d(x, y) \le d(x, z) + d(z, y) < 2r = d(x, y)$, a contradiction. So the balls are disjoint. A pseudometric space need not be $T_0$: in the example of Chapter 3 with $d((x,y),(x',y')) = |x - x'|$, the points $(0,0)$ and $(0,1)$ are inseparable.

**Counterexample (The cofinite topology).** Let $X$ be infinite with the cofinite topology. It is $T_1$, since finite sets are closed. It is not Hausdorff: two nonempty open sets have finite complements, and their intersection has a finite complement too, so it is not empty. Chapter 2 showed the consequence: a sequence of distinct points tends to each point of $X$, so limits are not unique.

**Counterexample (The Sierpiński space).** On $\{0, 1\}$ with the open sets $\emptyset$, $\{1\}$ and $\{0, 1\}$, the two points are distinguished by the open set $\{1\}$, so the space is $T_0$. It is not $T_1$: each open set that contains $0$ contains $1$.

**Counterexample (The line with two origins).** Let $X = (\mathbb{R} \times \{0, 1\})/{\sim}$, where $(t, 0) \sim (t, 1)$ for $t \ne 0$. It is a line with two copies $0_a = [(0,0)]$ and $0_b = [(0,1)]$ of the origin. Each point has a neighbourhood homeomorphic to an interval: for $0_a$, the image of $(-\varepsilon, \varepsilon) \times \{0\}$. The space is $T_1$: the preimage of a point under the quotient map is one or two points, a closed set. It is not Hausdorff: each neighbourhood of $0_a$ contains the points $t$ with $0 < |t| < \varepsilon$ for some $\varepsilon$, and so does each neighbourhood of $0_b$. The sequence $1/n$ tends to both origins. The example shows that "locally like $\mathbb{R}$" does not give the Hausdorff axiom, which is why the definition of a manifold asks for it.

### The library around it

The axioms $T_0$ and $T_1$ and the weaker axioms $R_0$ and $R_1$ are in `Mathlib.Topology.Separation.Basic`, and $T_2$ is in `Mathlib.Topology.Separation.Hausdorff`. The axiom $R_1$ says that two points either have disjoint neighbourhood filters or satisfy $\mathcal{N}(x) \le \mathcal{N}(y)$; it is the "Hausdorff up to inseparability" axiom, and a space is $T_2$ if and only if it is $R_1$ and $T_0$ (`instT2SpaceOfR1SpaceOfT0Space`). Mathlib states many results with these weaker axioms, so a reader sees `R1Space` where a textbook writes "Hausdorff".

Each metric space is Hausdorff by instance, so the uniqueness of limits applies to `ℝ` and `ℂ` without a hypothesis. The space `SeparationQuotient X` is the $T_0$ quotient of any space.

The module `Mathlib.Topology.SeparatedMap` gives the relative forms of the Hausdorff axiom for a map $f : X \to Y$. The map is separated if two distinct points with the same image have disjoint neighbourhoods (`IsSeparatedMap`, with `isSeparatedMap_iff_disjoint_nhds`), and locally injective if each point has a neighbourhood on which $f$ is injective (`IsLocallyInjective`, with `isLocallyInjective_iff_nhds`). The two notions say that the diagonal of the fibre product $X \times_Y X$ is closed or open (`isSeparatedMap_iff_isClosed_diagonal`, `isLocallyInjective_iff_isOpen_diagonal`). A space is Hausdorff if and only if its map to a point is separated (`t2space_iff_isSeparatedMap`). For a separated and locally injective map $p$, two continuous lifts of the same map from a connected space that agree at one point agree everywhere (`IsSeparatedMap.eqOn_of_comp_eqOn`). This is the uniqueness of lifts in the theory of covering spaces.

Some small modules add facts that mix separation with other properties. An infinite Hausdorff space contains an infinite discrete subspace (`exists_infinite_discreteTopology`) and a copy of $\mathbb{N}$ (`exists_topology_isEmbedding_nat`), in `Mathlib.Topology.NatEmbedding`. A nontrivial preconnected T1 space is infinite (`PreconnectedSpace.infinite`), and a totally disconnected space is T1 (`TotallyDisconnectedSpace.t1Space`), in `Mathlib.Topology.Separation.Connected`. The module `Mathlib.Topology.Separation.CountableSeparatingOn` gives countable separating families of open or closed sets in spaces with a countable basis. The module `Mathlib.Topology.Separation.DisjointCover` proves that each open cover of a compact zero-dimensional space has a finite refinement by disjoint clopen sets (`TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`), and that a continuous map on a compact totally disconnected Hausdorff space is near a locally constant map (`ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal`).

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that $X$ is $T_1$ if and only if $\{x\} = \bigcap \{U : U \text{ open}, x \in U\}$ for each $x$.
2. (A) Show that each finite $T_1$ space is discrete.
3. (A) Show that a sequence in a Hausdorff space has at most one limit, directly from the definition with open sets.
4. (B) Show that the image of a Hausdorff space under a continuous map need not be Hausdorff, and that a quotient of a Hausdorff space need not be Hausdorff.
5. (B) Let $f : X \to Y$ be continuous and $Y$ Hausdorff. Show that the graph $\{(x, f(x))\}$ is closed in $X \times Y$.
6. (B) Show that the Sorgenfrey line of Chapter 1 is Hausdorff.
7. (C) Let $X$ be a space. Show that the relation "$x$ and $y$ are inseparable" is an equivalence relation, that the quotient space is $T_0$, and that each continuous map from $X$ to a $T_0$ space factors through the quotient.

### Notes and history

The Hausdorff axiom is one of the axioms of a topological space in Hausdorff's *Grundzüge der Mengenlehre* (1914), and later authors dropped it from the definition. The names $T_0$ to $T_4$ come from Alexandroff and Hopf, *Topologie* (1935). Kolmogorov introduced the axiom $T_0$, and Fréchet and Riesz the axiom $T_1$. The filter proof of uniqueness of limits, through the disjointness of neighbourhood filters, is the proof of Bourbaki.

### Reference

<?reference?>
