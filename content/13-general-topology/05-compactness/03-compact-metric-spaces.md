---
title: Compact metric spaces and the Heine-Borel theorem
kind: theory
modules:
  - Mathlib.Topology.MetricSpace.ProperSpace
  - Mathlib.Topology.MetricSpace.Bounded
explains:
  E3: [TotallyBounded, IsSeqCompact, ProperSpace]
  E2: [Metric.totallyBounded_iff, isCompact_iff_isSeqCompact, IsCompact.isSeqCompact, IsSeqCompact.isCompact, IsCompact.tendsto_subseq, IsSeqCompact.totallyBounded, IsSeqCompact.isComplete, IsCompact.totallyBounded, IsCompact.isComplete, isCompact_iff_totallyBounded_isComplete, Ultrafilter.union_mem_iff, Ultrafilter.finite_biUnion_mem_iff, IsCompact.isBounded, ProperSpace.isCompact_closedBall, proper_of_compact, Metric.isCompact_of_isClosed_isBounded, Metric.isCompact_iff_isClosed_bounded, tendsto_subseq_of_bounded, lebesgue_number_lemma_of_metric]
  E1: auto
families: []
requires: [V13.C02, V13.C03, V13.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Compact metric spaces and the Heine-Borel theorem

### Overview

In a metric space, compactness has two more descriptions. A set is sequentially compact if each sequence in it has a subsequence that converges in it. A set is complete and totally bounded if its Cauchy sequences converge in it and, for each $\varepsilon > 0$, it is covered by finitely many balls of radius $\varepsilon$. The main theorem of this section says that compact, sequentially compact, and complete and totally bounded are the same in a metric space. The Heine-Borel theorem follows: in $\mathbb{R}^n$ a set is compact if and only if it is closed and bounded.

### Definitions

**Definition (Sequentially compact, totally bounded, complete set).** Let $K$ be a subset of a metric space $X$.

- $K$ is sequentially compact if each sequence in $K$ has a subsequence that converges to a point of $K$.
- $K$ is totally bounded if for each $\varepsilon > 0$ there is a finite set $T \subseteq X$ with $K \subseteq \bigcup_{y \in T} B(y, \varepsilon)$.
- $K$ is complete if each Cauchy sequence in $K$ converges to a point of $K$.

::: mathlib
`IsSeqCompact` · `Mathlib.Topology.Defs.Sequences`

`IsSeqCompact s`: each sequence in `s` has a strictly monotone `φ : ℕ → ℕ` with `x ∘ φ` convergent to a point of `s`. A subsequence is `x ∘ φ` with `StrictMono φ`.

<?decl IsSeqCompact?>
:::

::: mathlib
`TotallyBounded` · `Mathlib.Topology.UniformSpace.Cauchy`

Total boundedness is defined for uniform spaces (Chapter 7): for each entourage `d` there is a finite `t` with `s ⊆ ⋃ y ∈ t, {x | (x, y) ∈ d}`. `Metric.totallyBounded_iff` is the form with balls.

<?decl TotallyBounded?>
:::

::: mathlib
`Metric.totallyBounded_iff` · `Mathlib.Topology.MetricSpace.Pseudo.Basic`

Total boundedness with finite sets of centres of `ε`-balls.

<?decl Metric.totallyBounded_iff?>
:::

### Theorems and proofs

**Theorem (Compact metric spaces).** For a subset $K$ of a metric space the following are equivalent.

1. $K$ is compact.
2. $K$ is sequentially compact.
3. $K$ is complete and totally bounded.

*Proof.* (1 ⇒ 2) Let $(x_n)$ be a sequence in $K$. The image filter $F$ of $\mathrm{atTop}$ under $n \mapsto x_n$ is proper and contains $K$. Let $x \in K$ be a cluster point of $F$. Then each ball $B(x, r)$ meets each tail $\{x_m : m \ge n\}$, so it contains $x_m$ for infinitely many $m$. Choose $n_1 < n_2 < \dots$ inductively with $x_{n_k} \in B(x, 1/k)$. Then $x_{n_k} \to x$.

(2 ⇒ 3) A Cauchy sequence in $K$ has a subsequence that converges to some $x \in K$. A Cauchy sequence with a convergent subsequence converges to the same limit: if $d(x_m, x_n) < \varepsilon$ for $m, n \ge N$ and $d(x_{n_k}, x) < \varepsilon$ for some $n_k \ge N$, then $d(x_n, x) < 2\varepsilon$ for $n \ge N$. So $K$ is complete. Suppose $K$ is not totally bounded: for some $\varepsilon > 0$ no finite set of $\varepsilon$-balls covers $K$. Choose $x_0 \in K$, and inductively $x_n \in K \setminus \bigcup_{m < n} B(x_m, \varepsilon)$. Then $d(x_m, x_n) \ge \varepsilon$ for $m \ne n$. No subsequence is Cauchy, so none converges, against 2.

(3 ⇒ 1) By the ultrafilter form of compactness (Section 2), it suffices to show that an ultrafilter $U$ with $K \in U$ converges to a point of $K$. First a fact on ultrafilters: if a finite union $A_1 \cup \dots \cup A_m$ is in $U$, then some $A_j \in U$. Otherwise each $X \setminus A_j$ is in $U$, and so is their intersection, which misses the union.

For each $n$, $K$ is covered by finitely many balls of radius $2^{-n}$. Their union contains $K$, so it is in $U$, and by the fact one of the balls, $B_n$, is in $U$. The set $K \cap B_0 \cap \dots \cap B_n$ is in $U$, so it is nonempty; choose $x_n$ in it. For $m \ge n$, both $x_m$ and $x_n$ lie in $B_n$, so $d(x_m, x_n) < 2 \cdot 2^{-n}$. So $(x_n)$ is Cauchy, and since $K$ is complete, $x_n \to x$ for some $x \in K$.

The ultrafilter converges to $x$. Let $\varepsilon > 0$, and choose $n$ with $3 \cdot 2^{-n} < \varepsilon$. For $y \in B_n$ and $m \ge n$, $d(y, x_m) < 2 \cdot 2^{-n}$, since both lie in a ball of radius $2^{-n}$. Let $m \to \infty$: $d(y, x) \le 2 \cdot 2^{-n} < \varepsilon$. So $B_n \subseteq B(x, \varepsilon)$, and $B(x, \varepsilon) \in U$. Since the balls form a basis of $\mathcal{N}(x)$, $U \le \mathcal{N}(x)$. $\square$

::: mathlib
`isCompact_iff_isSeqCompact` · `Mathlib.Topology.Sequences`

The equivalence of 1 and 2, in each pseudometrizable space. The two directions are `IsCompact.isSeqCompact`, valid in each first countable space, and `IsSeqCompact.isCompact`. The form with an explicit subsequence is `IsCompact.tendsto_subseq`.

<?decl isCompact_iff_isSeqCompact?>
:::

::: mathlib
`IsCompact.tendsto_subseq` · `Mathlib.Topology.Sequences`

A sequence in a compact set of a first countable space has a convergent subsequence.

<?decl IsCompact.tendsto_subseq?>
:::

::: mathlib
`isCompact_iff_totallyBounded_isComplete` · `Mathlib.Topology.UniformSpace.Cauchy`

The equivalence of 1 and 3, in each uniform space, with the completeness of Chapter 7. The directions from compactness are `IsCompact.totallyBounded` and `IsCompact.isComplete`.

<?decl isCompact_iff_totallyBounded_isComplete?>
:::

::: mathlib
`IsSeqCompact.totallyBounded` · `Mathlib.Topology.Sequences`

The step 2 ⇒ 3 for total boundedness, in a uniform space. The completeness half is `IsSeqCompact.isComplete`, which needs a countably generated uniformity.

<?decl IsSeqCompact.totallyBounded?>
:::

::: mathlib
`Ultrafilter.finite_biUnion_mem_iff` · `Mathlib.Order.Filter.Ultrafilter.Basic`

The fact on finite unions used in step 3 ⇒ 1. The case of two sets is `Ultrafilter.union_mem_iff`.

<?decl Ultrafilter.finite_biUnion_mem_iff?>
:::

**Definition (Proper space).** A metric space is proper if each closed ball is compact.

::: mathlib
`ProperSpace` · `Mathlib.Topology.MetricSpace.ProperSpace`

A class with the field `isCompact_closedBall`. Each compact space is proper (`proper_of_compact`), and so are `ℝ`, `ℂ` and each finite dimensional normed space over them.

<?decl ProperSpace?>
:::

**Theorem (Heine-Borel).** In $\mathbb{R}^n$ a set is compact if and only if it is closed and bounded. More generally, in a proper metric space a set is compact if and only if it is closed and bounded.

*Proof.* A compact set $K$ in a metric space is closed (Chapter 4 and Section 1). It is bounded: it is covered by finitely many balls of radius $1$, and a finite union of balls is bounded.

Conversely, let $K$ be closed and bounded in a proper space, and nonempty. Fix $x \in K$. Since $K$ is bounded, $K \subseteq \bar B(x, r)$ for some $r$. The ball is compact, and $K$ is a closed subset of it, so $K$ is compact.

The space $\mathbb{R}^n$ with the max distance is proper: $\bar B(x, r) = \prod_k [x_k - r, x_k + r]$ is a box, which is compact by Section 2. $\square$

::: mathlib
`Metric.isCompact_iff_isClosed_bounded` · `Mathlib.Topology.MetricSpace.Bounded`

The theorem in a proper metric space. The directions are `IsCompact.isBounded` with `IsCompact.isClosed`, and `Metric.isCompact_of_isClosed_isBounded`.

<?decl Metric.isCompact_iff_isClosed_bounded?>
:::

::: mathlib
`Metric.isCompact_of_isClosed_isBounded` · `Mathlib.Topology.MetricSpace.Bounded`

A closed bounded set in a proper space is compact.

<?decl Metric.isCompact_of_isClosed_isBounded?>
:::

::: mathlib
`tendsto_subseq_of_bounded` · `Mathlib.Topology.MetricSpace.Sequences`

The Bolzano-Weierstrass theorem: a bounded sequence in a proper space has a subsequence that converges to a point of the closure of the set.

<?decl tendsto_subseq_of_bounded?>
:::

**Theorem (Lebesgue number).** Let $K$ be compact in a metric space and $(U_i)$ an open cover of $K$. There is a $\delta > 0$ such that each ball $B(x, \delta)$ with $x \in K$ lies in some $U_i$.

*Proof.* For each $x \in K$ choose $r_x > 0$ and $i$ with $B(x, 2 r_x) \subseteq U_i$. Finitely many balls $B(x_k, r_{x_k})$ cover $K$. Let $\delta = \min_k r_{x_k}$. For $x \in K$, choose $k$ with $x \in B(x_k, r_{x_k})$. Then $B(x, \delta) \subseteq B(x_k, r_{x_k} + \delta) \subseteq B(x_k, 2 r_{x_k})$, which lies in one $U_i$. $\square$

::: mathlib
`lebesgue_number_lemma_of_metric` · `Mathlib.Topology.MetricSpace.Pseudo.Lemmas`

The theorem.

<?decl lebesgue_number_lemma_of_metric?>
:::

### Examples

**Counterexample (Closed and bounded is not enough).** In $\mathbb{N}$ with the discrete metric, the whole space is closed and bounded, with diameter $1$. It is not compact: the open cover by points has no finite subcover. It is complete but not totally bounded. So the space is not proper, and Heine-Borel fails in it. The same holds for the closed unit ball of the space $\ell^2$ of square summable sequences, where the unit vectors $e_n$ satisfy $d(e_m, e_n) = \sqrt{2}$.

**Counterexample (Totally bounded is not enough).** The set $[0, 1] \cap \mathbb{Q}$ is totally bounded, since it is covered by the balls around the points $k/n$. It is not complete in $\mathbb{Q}$: a sequence of rationals that tends to $1/\sqrt{2}$ is Cauchy and has no limit in $\mathbb{Q}$. So it is not compact.

**Example (Uniform continuity on compact sets).** Let $f : K \to Y$ be continuous with $K$ a compact metric space. Then $f$ is uniformly continuous. Given $\varepsilon > 0$, the sets $U_x = f^{-1}(B(f(x), \varepsilon/2))$ form an open cover of $K$. Let $\delta$ be a Lebesgue number. If $d(x, y) < \delta$, then $x, y \in B(x, \delta) \subseteq U_z$ for some $z$, so $d(f(x), f(y)) < \varepsilon$. Chapter 7 states this theorem of Heine for uniform spaces.

### The library around it

The proper spaces are in `Mathlib.Topology.MetricSpace.ProperSpace`, and the Heine-Borel theorem in `Mathlib.Topology.MetricSpace.Bounded`. Sequential compactness is in `Mathlib.Topology.Sequences`, total boundedness and complete sets in `Mathlib.Topology.UniformSpace.Cauchy`. The proofs of Mathlib run in uniform spaces, and the metric statements are special cases. The finite dimensional normed spaces are proper by an instance in the volume on normed spaces, so the Heine-Borel theorem applies to `EuclideanSpace ℝ (Fin n)` and to `Fin n → ℝ`.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that a totally bounded set is bounded, and that a subset of a totally bounded set is totally bounded.
2. (A) Show that a compact metric space is separable.
3. (A) Use the Heine-Borel theorem to show that the unit sphere in $\mathbb{R}^n$ is compact.
4. (B) Show that the closure of a totally bounded set is totally bounded, and deduce that in a complete metric space a set has compact closure if and only if it is totally bounded.
5. (B) Let $K$ be compact and $f : K \to K$ with $d(f(x), f(y)) < d(x, y)$ for $x \ne y$. Show that $f$ has exactly one fixed point. Hint: minimise $x \mapsto d(x, f(x))$.
6. (B) Show that $\mathbb{R}$ with the metric $\min(|x - y|, 1)$ is not proper, although it has the same topology as $\mathbb{R}$.
7. (C) Show that a metric space is compact if and only if each continuous function to $\mathbb{R}$ is bounded.

### Notes and history

The equivalence of the three forms of compactness for metric spaces is due to Fréchet (1906), who defined "compact" as sequentially compact. Heine (1872) proved the uniform continuity of continuous functions on $[a, b]$ with a covering argument, and Borel (1895) isolated the covering lemma. The name Heine-Borel theorem is due to Schoenflies. The Lebesgue number lemma appears in Lebesgue's *Leçons sur l'intégration* (1904).

### Reference

<?reference?>
