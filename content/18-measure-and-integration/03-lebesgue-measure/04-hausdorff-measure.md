---
title: Hausdorff measure
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.Hausdorff
explains:
  E2: [MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory, MeasureTheory.OuterMeasure.mkMetric'_isMetric, MeasureTheory.Measure.hausdorffMeasure_apply, MeasureTheory.Measure.hausdorffMeasure_zero_or_top, LipschitzWith.hausdorffMeasure_image_le, Isometry.hausdorffMeasure_image, MeasureTheory.hausdorffMeasure_pi_real, MeasureTheory.hausdorffMeasure_segment]
  E1: auto
families: []
requires: [V13, V18.C01, V18.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Hausdorff measure

### Overview

The Lebesgue measure of $\mathbb{R}^n$ measures sets of dimension $n$. A curve in the plane or a surface in space has Lebesgue measure zero, but it still has a length or an area. The Hausdorff measures fill this gap. For each real number $d \ge 0$, the $d$ dimensional Hausdorff measure of a set $s$ in a metric space is

$$\mathcal{H}^d(s) = \lim_{r \to 0} \inf \left\{ \sum_n (\operatorname{diam} t_n)^d : s \subseteq \bigcup_n t_n, \ \operatorname{diam} t_n \le r \right\}.$$

The measure exists on each extended metric space, and it needs no group structure or coordinates. The measure $\mathcal{H}^1$ of a segment is its length, and on $\mathbb{R}^n$ the measure $\mathcal{H}^n$ is the Lebesgue measure. This section explains the construction through metric outer measures, the basic properties of $\mathcal{H}^d$, its behaviour under Lipschitz and Hölder maps, and its value on $\mathbb{R}^n$. All of it is in the file `Mathlib.MeasureTheory.Measure.Hausdorff`. The Hausdorff dimension, the critical value of $d$, is defined from these measures in another part of the library and is not in this section.

### The library around it

#### Metric outer measures

An outer measure $\mu$ on an extended metric space is metric, `MeasureTheory.OuterMeasure.IsMetric`, when $\mu(s \cup t) = \mu(s) + \mu(t)$ for each two sets $s, t$ at positive distance. The main theorem on these outer measures is `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`: every Borel set is Carathéodory measurable for a metric outer measure. With the theorem of Carathéodory of Chapter 2, a metric outer measure thus gives a Borel measure. The proof first shows that each closed set $F$ is measurable. For a test set $s$, it splits $s \setminus F$ into the shells of points at distance between $1/(n+1)$ and $1/n$ from $F$. Shells with indices of the same parity are at positive distance from each other, which gives the estimate.

The construction of Carathéodory gives a metric outer measure from any function $m$ on sets. For $r > 0$, the outer measure `MeasureTheory.OuterMeasure.mkMetric'.pre m r` is the largest outer measure that is at most $m(t)$ on the sets $t$ of diameter at most $r$. It increases as $r$ decreases to $0$, and `MeasureTheory.OuterMeasure.mkMetric' m` is the limit. This limit is always metric, `MeasureTheory.OuterMeasure.mkMetric'_isMetric`. The reason: if $s$ and $t$ are at distance more than $r$, no set of diameter at most $r$ meets both of them, so the covers of $s \cup t$ split into covers of $s$ and of $t$.

The special case where $m(t)$ depends only on the diameter of $t$ is `MeasureTheory.OuterMeasure.mkMetric`, which takes a function $m : [0, \infty] \to [0, \infty]$. The measure `MeasureTheory.Measure.mkMetric m` is its restriction to the Borel sets, and `MeasureTheory.Measure.mkMetric_apply` writes its value as the supremum over $r > 0$ of the infimum over covers. The comparison lemma `MeasureTheory.Measure.mkMetric_mono` says that $m_1 \le m_2$ near $0$ implies $\mu_{m_1} \le \mu_{m_2}$.

#### The Hausdorff measure

The measure `MeasureTheory.Measure.hausdorffMeasure d` is `MeasureTheory.Measure.mkMetric` for the function $t \mapsto t^d$. The notation is `μH[d]`, open in the namespace MeasureTheory. The formula of the overview is `MeasureTheory.Measure.hausdorffMeasure_apply`. In this formula, the empty sets of a cover count with $0$, also when $d = 0$. A lower bound comes from `MeasureTheory.Measure.le_hausdorffMeasure`: if a measure $\mu$ satisfies $\mu(s) \le (\operatorname{diam} s)^d$ for every set $s$ of small diameter, then $\mu \le \mathcal{H}^d$. Upper bounds come from explicit covers, `MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum`: a sequence of finite covers with diameters that tend to $0$ bounds $\mathcal{H}^d(s)$ by the lower limit of the sums.

The dependence on $d$ has a jump. The measures decrease in $d$, `MeasureTheory.Measure.hausdorffMeasure_mono`. For $d_1 < d_2$, `MeasureTheory.Measure.hausdorffMeasure_zero_or_top` says that $\mathcal{H}^{d_2}(s) = 0$ or $\mathcal{H}^{d_1}(s) = \infty$. The proof compares the sums: $(\operatorname{diam} t)^{d_2} \le r^{d_2 - d_1} (\operatorname{diam} t)^{d_1}$ when $\operatorname{diam} t \le r$. So there is at most one value of $d$ where $\mathcal{H}^d(s)$ is positive and finite. This critical value is the Hausdorff dimension.

The measure $\mathcal{H}^0$ is the counting measure: a singleton has measure $1$, `MeasureTheory.Measure.hausdorffMeasure_zero_singleton`, and a nonempty set has measure at least $1$, `MeasureTheory.Measure.one_le_hausdorffMeasure_zero_of_nonempty`. For $d > 0$ points are null sets, `MeasureTheory.Measure.nullSingletonClass_hausdorff`. A set of finite $\mathcal{H}^d$ measure is separable, `MeasureTheory.Measure.isSeparable_of_hausdorffMeasure_ne_top`.

#### Maps

Lipschitz maps can only decrease the Hausdorff measure, up to a constant. If $f$ is $K$ Lipschitz and $d \ge 0$, then `LipschitzWith.hausdorffMeasure_image_le` gives $\mathcal{H}^d(f(s)) \le K^d \mathcal{H}^d(s)$; the version on a set is `LipschitzOnWith.hausdorffMeasure_image_le`. The proof sends each cover of $s$ to the images, whose diameters are at most $K$ times larger. The Hölder version `HolderOnWith.hausdorffMeasure_image_le` changes the dimension: an $r$ Hölder map gives $\mathcal{H}^d(f(s)) \le C^d \mathcal{H}^{rd}(s)$. Antilipschitz maps give the inequality in the other direction, `AntilipschitzWith.le_hausdorffMeasure_image`.

An isometry keeps the measure, `Isometry.hausdorffMeasure_image`, with the hypothesis $d \ge 0$ or a surjective map. An isometric equivalence is measure preserving, `IsometryEquiv.measurePreserving_hausdorffMeasure`. So the Hausdorff measure is invariant under translations, `MeasureTheory.hausdorffMeasure_vadd`, and under isometric actions, `MeasureTheory.hausdorffMeasure_smul`. Scaling by $c$ multiplies $\mathcal{H}^d$ by $|c|^d$: `MeasureTheory.Measure.hausdorffMeasure_smul₀` in a normed space and `MeasureTheory.hausdorffMeasure_homothety_image` for a homothety of an affine space. An orthogonal projection is $1$ Lipschitz, so it does not increase the measure, `MeasureTheory.hausdorffMeasure_orthogonalProjectionOnto_le`.

#### The Hausdorff measure of the real spaces

The main comparison is `MeasureTheory.hausdorffMeasure_pi_real`: on `ι → ℝ` for a finite type $\iota$ with $n$ elements, $\mathcal{H}^n$ is the Lebesgue measure `MeasureTheory.MeasureSpace.volume`. The special cases are `MeasureTheory.hausdorffMeasure_real` for $\mathbb{R}$ and `MeasureTheory.hausdorffMeasure_prod_real` for `ℝ × ℝ`. The proof uses the sup distance of these types. For the inequality $\lambda \le \mathcal{H}^n$, a set of diameter $\delta$ lies in a cube of side $\delta$, which has volume $\delta^n$. For the other inequality, a box is the union of $k^n$ small cubes of side $1/k$ times its sides, and these covers give the volume of the box in the limit.

In a real normed space, `MeasureTheory.hausdorffMeasure_segment` gives the length of a segment: $\mathcal{H}^1([x, y]) = d(x, y)$. The affine version is `MeasureTheory.hausdorffMeasure_affineSegment`. More generally, `MeasureTheory.hausdorffMeasure_lineMap_image` says that the image of a set $s \subseteq \mathbb{R}$ under the affine map $t \mapsto x + t(y - x)$ has measure $d(x, y) \, \mathcal{H}^1(s)$.

#### Common errors

1. Expecting the normalization of textbooks. Many texts multiply $(\operatorname{diam} t)^d$ by the volume of the unit ball of dimension $d$ divided by $2^d$, so that $\mathcal{H}^n$ is the Lebesgue measure for the Euclidean distance. Mathlib has no such factor. The equality `MeasureTheory.hausdorffMeasure_pi_real` holds for the sup distance of `ι → ℝ`; on `EuclideanSpace ℝ ι` the two measures differ by a constant.
2. Forgetting the hypothesis $0 \le d$. For $d < 0$, the function $t \mapsto t^d$ is decreasing, and lemmas such as `LipschitzWith.hausdorffMeasure_image_le` fail. Most lemmas of the file have $0 \le d$ as a hypothesis.
3. Applying `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory` to an outer measure that is additive only on sets that are disjoint. A metric outer measure needs additivity for sets at positive distance, not for all disjoint sets, and the proof uses exactly this property.

### Exercises

1. (A) Show that $\mathcal{H}^0(s)$ is the number of points of a finite set $s$.
2. (A) Use `LipschitzWith.hausdorffMeasure_image_le` to show that the graph of a $1$ Lipschitz function $f : [0, 1] \to \mathbb{R}$ has finite $\mathcal{H}^1$ measure, for the sup distance on `ℝ × ℝ`.
3. (B) Show that a segment in $\mathbb{R}^2$ has $\mathcal{H}^2$ measure zero, with `MeasureTheory.Measure.hausdorffMeasure_zero_or_top` and `MeasureTheory.hausdorffMeasure_segment`.
4. (B) Let $C$ be the middle third Cantor set. Use the covers by $2^k$ intervals of length $3^{-k}$ and `MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum` to show that $\mathcal{H}^d(C) \le 1$ for $d = \log 2 / \log 3$.
5. (B) Prove that a metric outer measure is additive on two disjoint compact sets.
6. (C) Prove `MeasureTheory.hausdorffMeasure_real`, the equality $\mathcal{H}^1 = \lambda$ on $\mathbb{R}$, directly from the definition.

### Reference

<?reference?>
