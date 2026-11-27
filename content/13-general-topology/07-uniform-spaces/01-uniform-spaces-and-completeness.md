---
title: Uniform spaces, Cauchy filters and completeness
kind: theory
modules:
  - Mathlib.Topology.UniformSpace.Defs
  - Mathlib.Topology.UniformSpace.Cauchy
  - Mathlib.Topology.UniformSpace.HeineCantor
explains:
  E3: [UniformSpace, Cauchy, CauchySeq, CompleteSpace, IsComplete]
  E2: [uniformity, UniformContinuous, Metric.mem_uniformity_dist, Metric.uniformContinuous_iff, UniformContinuous.continuous, CompactSpace.uniformContinuous_of_continuous, IsCompact.uniformContinuousOn_of_continuous, cauchy_nhds, Cauchy.mono, Cauchy.map, Filter.Tendsto.cauchySeq, le_nhds_of_cauchy_adhp, IsClosed.isComplete, IsComplete.isClosed, completeSpace_iff_isComplete_univ, UniformSpace.complete_of_cauchySeq_tendsto, Real.instCompleteSpace]
  E1: auto
families: []
requires: [V13.C01, V13.C02, V13.C03, V13.C04, V13.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Uniform spaces, Cauchy filters and completeness

### Overview

In a metric space, the sets $V_\varepsilon = \{(x, y) : d(x, y) < \varepsilon\}$ say when two points are $\varepsilon$-close. A uniform space keeps only the filter that these sets generate on $X \times X$. This filter is enough to define uniform continuity, Cauchy filters and completeness, and it gives a topology. This section states the definitions, proves the theorem of Heine, and gives the basic facts on complete sets, with the example that $\mathbb{Q}$ is not complete.

### Definitions

For relations $V, W \subseteq X \times X$, write $V^{-1} = \{(y, x) : (x, y) \in V\}$ and $V \circ W = \{(x, z) : \exists y, (x, y) \in V, (y, z) \in W\}$. The diagonal is $\Delta = \{(x, x)\}$.

**Definition (Uniform space).** A uniform structure on $X$ is a filter $\mathcal{U}$ on $X \times X$, whose members are called entourages, such that:

1. each entourage contains $\Delta$;
2. if $V \in \mathcal{U}$, then $V^{-1} \in \mathcal{U}$;
3. for each $V \in \mathcal{U}$ there is $W \in \mathcal{U}$ with $W \circ W \subseteq V$.

Its topology has the neighbourhood filters $\mathcal{N}(x) = \{V[x] : V \in \mathcal{U}\}$, where $V[x] = \{y : (x, y) \in V\}$.

Axiom 3 is the triangle inequality in disguise: for a metric, $V_{\varepsilon/2} \circ V_{\varepsilon/2} \subseteq V_\varepsilon$.

::: mathlib
`UniformSpace` · `Mathlib.Topology.UniformSpace.Defs`

A class with the filter `uniformity α`, written `𝓤 α`, the three axioms in filter form, and a topology that must agree with the one above. Each metric space has this instance, and `Metric.mem_uniformity_dist` says that `s ∈ 𝓤 α` if and only if `s` contains some `{p | dist p.1 p.2 < ε}`.

<?decl UniformSpace?>
:::

**Definition (Uniform continuity).** A map $f : X \to Y$ of uniform spaces is uniformly continuous if for each entourage $W$ of $Y$, the set $\{(x, x') : (f(x), f(x')) \in W\}$ is an entourage of $X$. In filter language, $(f \times f)$ tends to $\mathcal{U}_Y$ along $\mathcal{U}_X$.

::: mathlib
`UniformContinuous` · `Mathlib.Topology.UniformSpace.Defs`

`Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)`. For metric spaces, `Metric.uniformContinuous_iff` gives the $\varepsilon$-$\delta$ form with one $\delta$ for all points. `UniformContinuous.continuous` gives continuity.

<?decl UniformContinuous?>
:::

**Definition (Cauchy filter, complete).** A filter $F$ on $X$ is Cauchy if it is proper and $F \times F \le \mathcal{U}$: for each entourage $V$ there is $A \in F$ with $A \times A \subseteq V$. A sequence is Cauchy if its image filter of $\mathrm{atTop}$ is Cauchy. A set $K$ is complete if each Cauchy filter $F$ with $K \in F$ converges to a point of $K$. The space is complete if $X$ is a complete set.

For a metric, $A \times A \subseteq V_\varepsilon$ says that $A$ has diameter at most $\varepsilon$. So a sequence is Cauchy if and only if, for each $\varepsilon$, some tail has small diameter: the definition of Chapter 3.

::: mathlib
`Cauchy` · `Mathlib.Topology.UniformSpace.Cauchy`

`Cauchy f` is `NeBot f ∧ f ×ˢ f ≤ 𝓤 α`. The rules `Cauchy.mono` (a finer proper filter is Cauchy) and `Cauchy.map` (images under uniformly continuous maps) are the ones used most.

<?decl Cauchy?>
:::

::: mathlib
`CauchySeq` · `Mathlib.Topology.UniformSpace.Cauchy`

`Cauchy (atTop.map u)`. A convergent sequence is Cauchy by `Filter.Tendsto.cauchySeq`.

<?decl CauchySeq?>
:::

::: mathlib
`CompleteSpace` · `Mathlib.Topology.UniformSpace.Cauchy`

The class with the field `complete`: each Cauchy filter converges. `UniformSpace.complete_of_cauchySeq_tendsto` reduces it to sequences when the uniformity is countably generated, as for metric spaces. `Real.instCompleteSpace` is the instance for `ℝ`.

<?decl CompleteSpace?>
:::

::: mathlib
`IsComplete` · `Mathlib.Topology.UniformSpace.Cauchy`

A complete set: each Cauchy filter `f ≤ 𝓟 s` has a limit in `s`. `completeSpace_iff_isComplete_univ` relates it to the class.

<?decl IsComplete?>
:::

### Theorems and proofs

**Theorem (Convergent filters are Cauchy).** If $F$ is proper and $F \le \mathcal{N}(x)$, then $F$ is Cauchy. If a Cauchy filter $F$ has a cluster point $x$, then $F \to x$.

*Proof.* Let $V$ be an entourage, and $W$ a symmetric entourage with $W \circ W \subseteq V$. Then $W[x] \in F$, and for $y, z \in W[x]$, $(y, x) \in W$ and $(x, z) \in W$, so $(y, z) \in V$. This proves the first claim.

For the second, let $V$ be an entourage, and $W$ symmetric with $W \circ W \subseteq V$. Choose $A \in F$ with $A \times A \subseteq W$. Since $x$ is a cluster point, $A$ meets $W[x]$ at some $a$. For each $y \in A$, $(x, a) \in W$ and $(a, y) \in W$, so $y \in V[x]$. So $V[x] \in F$. $\square$

::: mathlib
`le_nhds_of_cauchy_adhp` · `Mathlib.Topology.UniformSpace.Cauchy`

The second claim. The first is `cauchy_nhds` for the filter `𝓝 a`, with `Cauchy.mono`.

<?decl le_nhds_of_cauchy_adhp?>
:::

**Theorem (Complete and closed sets).** A closed subset of a complete space is complete. In a Hausdorff uniform space, a complete set is closed.

*Proof.* Let $K$ be closed in a complete space, and $F$ Cauchy with $K \in F$. Then $F \to x$ for some $x$. Each neighbourhood of $x$ is in $F$, so it meets $K$, and $x \in \overline{K} = K$.

Let $K$ be complete and $x \in \overline{K}$. The filter $F = \mathcal{N}(x) \sqcap \mathcal{P}(K)$ is proper and finer than $\mathcal{N}(x)$, so it is Cauchy. It contains $K$, so it converges to some $y \in K$. It also converges to $x$, and limits are unique in a Hausdorff space, so $x = y \in K$. $\square$

::: mathlib
`IsClosed.isComplete` · `Mathlib.Topology.UniformSpace.Cauchy`

The first claim. The second is `IsComplete.isClosed`, with a `T2Space` hypothesis.

<?decl IsClosed.isComplete?>
:::

**Theorem (Heine).** A continuous map $f : X \to Y$ from a compact uniform space is uniformly continuous.

*Proof.* Let $W$ be an entourage of $Y$, and $W'$ a symmetric entourage with $W' \circ W' \subseteq W$. Let $D = \{(x, x') : (f(x), f(x')) \in W\}$, and suppose that $D$ is not an entourage. Then each entourage $V$ meets the complement of $D$, so the filter $G = \mathcal{U}_X \sqcap \mathcal{P}((X \times X) \setminus D)$ is proper. Its image under the first projection is a proper filter on the compact space $X$, so it has a cluster point $a$.

By continuity at $a$, $P = f^{-1}(W'[f(a)])$ is a neighbourhood of $a$. Choose an entourage $V$ with $(V \circ V)[a] \subseteq P$. The set $V \setminus D$ is in $G$, so its first projection meets the neighbourhood $V[a]$. So there is $(x, x') \in V \setminus D$ with $(a, x) \in V$. Then $x \in P$, and $(a, x') \in V \circ V$, so $x' \in P$. Both $f(x)$ and $f(x')$ lie in $W'[f(a)]$, and since $W'$ is symmetric, $(f(x), f(x')) \in W' \circ W' \subseteq W$. So $(x, x') \in D$, a contradiction. $\square$

::: mathlib
`CompactSpace.uniformContinuous_of_continuous` · `Mathlib.Topology.UniformSpace.HeineCantor`

The theorem. `IsCompact.uniformContinuousOn_of_continuous` is the version for a compact subset.

<?decl CompactSpace.uniformContinuous_of_continuous?>
:::

### Examples

**Counterexample ($\mathbb{Q}$ is not complete).** Define rationals $a_0 = 1$, $b_0 = 2$, and bisect: with $m = (a_n + b_n)/2$, set $(a_{n+1}, b_{n+1}) = (m, b_n)$ if $m^2 < 2$ and $(a_n, m)$ otherwise. Since no rational has square $2$, the second case means $m^2 > 2$. By induction $a_n^2 < 2 < b_n^2$, $a_n \le a_{n+1} \le b_{n+1} \le b_n$, and $b_n - a_n = 2^{-n}$. For $m \ge n$, $|a_m - a_n| \le 2^{-n}$, so $(a_n)$ is Cauchy in $\mathbb{Q}$. Suppose $a_n \to q \in \mathbb{Q}$. Then $b_n = a_n + 2^{-n} \to q$ too. Squaring is continuous, so $a_n^2 \to q^2$ and $b_n^2 \to q^2$. From $a_n^2 < 2 < b_n^2$, $q^2 \le 2 \le q^2$, and $q^2 = 2$. This is impossible. So $\mathbb{Q}$ is not complete. The same sequence converges to $\sqrt{2}$ in $\mathbb{R}$, which is complete.

**Example (A uniform structure that is not from a metric).** Let $X = \mathbb{R}^{\mathbb{R}}$ with the entourages that contain a set $\{(f, g) : |f(t) - g(t)| < \varepsilon \text{ for } t \in T\}$, with $T$ finite and $\varepsilon > 0$. This is the uniformity of pointwise convergence. Its topology is the product topology, which is not first countable, so no metric gives it. It is complete: a Cauchy filter gives a Cauchy filter in each coordinate.

**Counterexample (Continuous but not uniformly continuous).** The map $x \mapsto x^2$ on $\mathbb{R}$ is continuous and not uniformly continuous: $(n + 1/n)^2 - n^2 > 2$ while the points are $1/n$ apart. On the compact set $[0, 1]$ the theorem of Heine applies.

### The library around it

The definitions are in `Mathlib.Topology.UniformSpace.Defs`, the Cauchy filters and complete sets in `Mathlib.Topology.UniformSpace.Cauchy`, and the theorem of Heine in `Mathlib.Topology.UniformSpace.HeineCantor`. The completeness of `ℝ` is in `Mathlib.Topology.UniformSpace.Real`. Each metric space carries a uniform structure, and all metric statements about Cauchy sequences, such as `Metric.cauchySeq_iff` of Chapter 3, are special cases. Topological groups also carry a uniform structure; the volume on topological algebra treats it.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that a uniformly continuous map sends Cauchy sequences to Cauchy sequences.
2. (A) Show that the discrete uniformity, with $\Delta$ as an entourage, makes each set complete.
3. (A) Show that $(0, 1)$ is not complete with the usual metric, although it is homeomorphic to the complete space $\mathbb{R}$.
4. (B) Show that a product of two complete uniform spaces is complete.
5. (B) Show that a compact uniform space is complete.
6. (B) Show that $x \mapsto 1/x$ is not uniformly continuous on $(0, 1)$ and is uniformly continuous on $[1, \infty)$.
7. (C) Show that on a compact Hausdorff space there is exactly one uniform structure that gives its topology.

### Notes and history

Weil introduced uniform spaces in 1937, and Bourbaki made them the basis of the general topology of analysis. Cauchy filters replace Cauchy sequences when the uniformity is not countably generated. Heine proved the theorem on uniform continuity for intervals in 1872; Cantor had used it before. Mathlib follows Bourbaki and defines completeness with filters, so the metric form is a theorem.

### Reference

<?reference?>
