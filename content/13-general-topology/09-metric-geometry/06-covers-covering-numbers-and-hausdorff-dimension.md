---
title: Covers, covering numbers and Hausdorff dimension
kind: api
modules:
  - Mathlib.Topology.MetricSpace.Cover
  - Mathlib.Topology.MetricSpace.MetricSeparated
  - Mathlib.Topology.MetricSpace.CoveringNumbers
  - Mathlib.Topology.MetricSpace.CoveringExponent
  - Mathlib.Topology.EMetricSpace.PairReduction
  - Mathlib.Topology.MetricSpace.HausdorffDimension
  - Mathlib.Topology.Connected.HausdorffMeasure
explains:
  E2: [Metric.IsCover.image_lipschitz, Metric.AreSeparated.finite_iUnion_left_iff, Metric.coveringNumber_le_packingNumber, Metric.packingNumber_two_mul_le_externalCoveringNumber, Metric.coveringNumber_subset_le, Metric.HasCoveringExponent.subset, dimH_union, dimH_countable, LipschitzWith.dimH_image_le, dense_compl_of_dimH_lt_finrank]
  E1: auto
families: []
requires: [V13.C01, V13.C03, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Covers, covering numbers and Hausdorff dimension

### Overview

A totally bounded set can be covered by finitely many balls of each radius $\varepsilon > 0$. The number of balls that are needed, as a function of $\varepsilon$, measures the size of the set at small scales. For the unit cube in $\mathbb{R}^d$ it grows like $\varepsilon^{-d}$, and the exponent $d$ is a notion of dimension. The modules of this section give names to these quantities: $\varepsilon$-covers, $\varepsilon$-separated sets, covering numbers and packing numbers, and a covering exponent. A lemma on pairs of points from the theory of stochastic processes also uses covers and is in this section.

The last module defines the Hausdorff dimension, a finer notion of dimension. It is defined through the Hausdorff measures of the measure theory volume, but most of its properties are statements about metric spaces only: monotonicity, countable unions, and the behaviour under Lipschitz and Hölder maps. This section states these properties and describes the measure theory that is behind them in words. All the definitions work in extended pseudometric spaces, so the distance is `edist` and its values are in $[0, \infty]$.

### The library around it

#### Covers and separated sets

Let $\varepsilon \ge 0$ be in `ℝ≥0`. A set $N$ is an $\varepsilon$-cover of $s$, written `Metric.IsCover ε s N`, if each point of $s$ is at distance at most $\varepsilon$ from a point of $N$. The set $N$ need not be a subset of $s$. In a pseudometric space this says that $s$ is in the union of the closed balls of radius $\varepsilon$ around the points of $N$ (`Metric.isCover_iff_subset_iUnion_closedBall`). The definition is an instance of the covers of a relation in Volume 1, for the relation $d(x, y) \le \varepsilon$.

A set $C$ is $\varepsilon$-separated, written `Metric.IsSeparated ε C`, if two distinct points of $C$ are at distance more than $\varepsilon$. Here $\varepsilon$ is in $[0, \infty]$. The two notions are dual. A maximal $\varepsilon$-separated subset of $s$ is an $\varepsilon$-cover of $s$ (`Metric.IsCover.of_maximal_isSeparated`): a point of $s$ that is far from all points of $N$ could be added to $N$.

| Lean name | Statement |
|---|---|
| `Metric.IsCover.mono` | a larger $N$ is still a cover |
| `Metric.IsCover.anti` | $N$ covers each subset of $s$ |
| `Metric.IsCover.mono_radius` | a cover for $\varepsilon$ is a cover for each $\delta \ge \varepsilon$ |
| `Metric.IsCover.refl` | $s$ covers itself for each $\varepsilon$ |
| `Metric.IsCover.singleton_of_ediam_le` | one point of $s$ covers $s$ if $\mathrm{diam}\, s \le \varepsilon$ |
| `Metric.IsSeparated.subset` | a subset of a separated set is separated |
| `Metric.IsSeparated.insert` | add a point that is far from the others |
| `Metric.exists_finite_isCover_of_totallyBounded` | a totally bounded set has a finite $\varepsilon$-cover in it, for $\varepsilon > 0$ |
| `Metric.isCompact_closure_iff_exists_finite_isCover` | in a proper space, $\overline{s}$ is compact if and only if $s$ has a finite $\varepsilon$-cover in it |

**Proposition** (`Metric.IsCover.image_lipschitz`). If $N$ is an $\varepsilon$-cover of $s$ and $f$ is $K$-Lipschitz, then $f(N)$ is a $K\varepsilon$-cover of $f(s)$.

*Proof.* Let $x \in s$ and choose $y \in N$ with $d(x, y) \le \varepsilon$. Then $d(f(x), f(y)) \le K d(x, y) \le K \varepsilon$.

The dual statement is `Metric.IsSeparated.image_antilipschitz`: an antilipschitz map with constant $K > 0$ sends an $\varepsilon$-separated set to an $\varepsilon/K$-separated set.

#### Separated pairs of sets

The module `Mathlib.Topology.MetricSpace.MetricSeparated` also has a notion for two sets. The sets $s$ and $t$ are metric separated, `Metric.AreSeparated s t`, if there is $r > 0$ with $r \le d(x, y)$ for all $x \in s$ and $y \in t$. Such sets are disjoint (`Metric.AreSeparated.disjoint`), and the relation is symmetric (`Metric.AreSeparated.symm`) and decreases with the sets (`Metric.AreSeparated.mono`). The notion is used in measure theory: an outer measure that is additive on metric separated pairs makes the Borel sets measurable.

**Proposition** (`Metric.AreSeparated.finite_iUnion_left_iff`). For a finite index set $I$, the union $\bigcup_{i \in I} s_i$ is metric separated from $t$ if and only if each $s_i$ is.

*Proof.* One direction is `Metric.AreSeparated.mono`. For the other, let $r_i > 0$ be a separation constant of $s_i$ and $t$. The minimum of the finitely many $r_i$ is positive and works for the union.

The finiteness of $I$ is necessary: the points $1/n$ are each metric separated from $\{0\}$, but their union is not. The lemmas `Metric.AreSeparated.union_left_iff` and `Metric.AreSeparated.finset_iUnion_left_iff` are the forms for two sets and for a `Finset`.

#### Covering numbers and packing numbers

The module `Mathlib.Topology.MetricSpace.CoveringNumbers` defines three numbers in `ℕ∞` for a set $A$ and a radius $\varepsilon$.

| Lean name | Definition |
|---|---|
| `Metric.externalCoveringNumber ε A` | the least cardinality of an $\varepsilon$-cover of $A$ |
| `Metric.coveringNumber ε A` | the least cardinality of an $\varepsilon$-cover of $A$ that is a subset of $A$ |
| `Metric.packingNumber ε A` | the greatest cardinality of an $\varepsilon$-separated subset of $A$ |

All three are infinite when no finite set works. The cardinality is `Set.encard`, so infinite sets have cardinality $\top$. The covering numbers decrease when $\varepsilon$ increases (`Metric.coveringNumber_anti`), and they are $1$ for a nonempty set of diameter at most $\varepsilon$ (`Metric.coveringNumber_eq_one_of_ediam_le`). In a metric space the covering number at radius $0$ is the cardinality of $A$ (`Metric.coveringNumber_zero`). When a number is finite, it is attained: `Metric.minimalCover ε A` is a cover of the minimal size (`Metric.encard_minimalCover`), and `Metric.maximalSeparatedSet ε A` is a separated set of the maximal size. The external covering number is at most the internal one (`Metric.externalCoveringNumber_le_coveringNumber`). The three numbers are comparable up to a factor $2$ in the radius.

**Proposition** (`Metric.coveringNumber_le_packingNumber`). $\mathrm{cov}(\varepsilon, A) \le \mathrm{pack}(\varepsilon, A)$.

*Proof.* If the packing number is infinite, there is nothing to prove. Otherwise `Metric.maximalSeparatedSet ε A` is an $\varepsilon$-separated subset of $A$ of maximal size. It is maximal for inclusion, so it is an $\varepsilon$-cover of $A$ (`Metric.isCover_maximalSeparatedSet`). Its cardinality is the packing number.

**Proposition** (`Metric.packingNumber_two_mul_le_externalCoveringNumber`). $\mathrm{pack}(2\varepsilon, A) \le \mathrm{cov}_{\mathrm{ext}}(\varepsilon, A)$.

*Proof.* Let $N$ be an $\varepsilon$-cover of $A$ and let $C \subseteq A$ be $2\varepsilon$-separated. Send each point of $C$ to a point of $N$ at distance at most $\varepsilon$. Two points of $C$ with the same image are at distance at most $2\varepsilon$, so they are equal. So the map is injective and $|C| \le |N|$.

The same idea gives `Metric.coveringNumber_two_mul_le_externalCoveringNumber`: an external $\varepsilon$-cover gives an internal $2\varepsilon$-cover. Choose a point of $A$ in each ball that meets $A$. So the internal and the external numbers have the same growth as $\varepsilon \to 0$.

**Proposition** (`Metric.coveringNumber_subset_le`). If $A \subseteq B$, then $\mathrm{cov}(\varepsilon, A) \le \mathrm{cov}(\varepsilon/2, B)$.

*Proof.* An internal $\varepsilon/2$-cover of $B$ is an external $\varepsilon/2$-cover of $A$. Apply `Metric.coveringNumber_two_mul_le_externalCoveringNumber` with the radius $\varepsilon/2$.

The halving of the radius is necessary because the internal covering number is not monotone in the set. The external one is monotone (`Metric.externalCoveringNumber_mono_set`). An isometry preserves the covering numbers (`Isometry.coveringNumber_image`).

#### The covering exponent

The structure `Metric.HasCoveringExponent A c d` says that $A$ has finite diameter and that
$$\mathrm{cov}(\varepsilon, A) \le c \, \varepsilon^{-d}$$
for each $\varepsilon$ with $0 < \varepsilon \le \mathrm{diam}\, A$. Its fields are `Metric.HasCoveringExponent.ediam_lt_top` and `Metric.HasCoveringExponent.coveringNumber_le`, and the constructor is `Metric.HasCoveringExponent.mk`. A bounded set in $\mathbb{R}^d$ has covering exponent $d$. The consequence `Metric.HasCoveringExponent.coveringNumber_lt_top` gives finite covering numbers for $\varepsilon > 0$.

**Proposition** (`Metric.HasCoveringExponent.subset`). If $A$ has covering exponent $d \ge 0$ with constant $c$ and $B \subseteq A$, then $B$ has covering exponent $d$ with constant $2^d c$.

*Proof sketch.* By `Metric.coveringNumber_subset_le`, $\mathrm{cov}(\varepsilon, B) \le \mathrm{cov}(\varepsilon/2, A) \le c\,(\varepsilon/2)^{-d} = 2^d c\, \varepsilon^{-d}$. The bound applies because $\varepsilon/2 \le \mathrm{diam}\, B \le \mathrm{diam}\, A$.

#### The pair reduction lemma

The module `Mathlib.Topology.EMetricSpace.PairReduction` proves one combinatorial result for the chaining method of probability theory. Let $J$ be a finite set of points with $|J| \le a^n$ and let $c \ge 0$. The theorem `EMetric.pair_reduction` gives a set $K$ of pairs of points of $J$ such that:

1. $K$ has at most $a |J|$ elements;
2. each pair $(s, t)$ of $K$ has $d(s, t) \le n c$;
3. for each map $f$ to a pseudometric space, $\sup \{ d(f(s), f(t)) : s, t \in J,\ d(s, t) \le c \} \le 2 \sup_{(s, t) \in K} d(f(s), f(t))$.

So the supremum over all close pairs, of which there can be $|J|^2$, is controlled by a supremum over only $a|J|$ pairs. In an estimate of an expected supremum, this replaces a factor $|J|^2$ by a factor $|J| \log |J|$. The proof is a greedy construction. It picks a point, takes the smallest $k$ such that the ball of radius $k c$ around it has at most $a^k$ points (`PairReduction.logSizeRadius`), adds the pairs of the point with that ball, removes a smaller ball, and repeats (`PairReduction.logSizeBallSeq`). The other declarations of the namespace PairReduction are steps of this proof.

#### Hausdorff dimension

The module `Mathlib.Topology.MetricSpace.HausdorffDimension` defines `dimH s` in $[0, \infty]$ for a set $s$ of an extended metric space. The definition uses the $d$-dimensional Hausdorff measures $\mu_H^d$ of the measure theory volume. For each $d$, $\mu_H^d(s)$ is the limit as $\delta \to 0$ of the infimum of $\sum_i (\mathrm{diam}\, U_i)^d$ over the countable covers of $s$ by sets of diameter at most $\delta$. The function $d \mapsto \mu_H^d(s)$ jumps from $\infty$ to $0$ at one value, and this value is $\mathrm{dimH}(s)$. The definition takes the supremum of the $d$ with $\mu_H^d(s) = \infty$ (`dimH_def`). The lemmas `hausdorffMeasure_of_lt_dimH`, `hausdorffMeasure_of_dimH_lt`, `dimH_le_of_hausdorffMeasure_ne_top` and `le_dimH_of_hausdorffMeasure_ne_zero` state the jump in Lean. The reader needs only two facts about Hausdorff measures for the proofs of this section: $\mu_H^d$ is countably subadditive, and a $K$-Lipschitz map multiplies $\mu_H^d$ by at most $K^d$. The definition does not need a measurable structure on the space, because it uses the Borel structure internally.

**Proposition** (`dimH_union`). $\mathrm{dimH}(s \cup t) = \max(\mathrm{dimH}(s), \mathrm{dimH}(t))$.

*Proof sketch.* The inequality $\ge$ is `dimH_mono`. For $\le$, let $d$ be above both dimensions. Then $\mu_H^d(s) = \mu_H^d(t) = 0$, so $\mu_H^d(s \cup t) = 0$ by subadditivity, and $\mathrm{dimH}(s \cup t) \le d$.

The same argument with countable subadditivity gives `dimH_iUnion` for a countable family.

**Proposition** (`dimH_countable`). A countable set has Hausdorff dimension $0$.

*Proof.* A point has dimension $0$ (`dimH_singleton`), because $\mu_H^d$ of a point is $0$ for $d > 0$. A countable set is a countable union of points, and `dimH_bUnion` gives the supremum of the dimensions, which is $0$.

**Proposition** (`LipschitzWith.dimH_image_le`). A Lipschitz map does not increase the Hausdorff dimension: $\mathrm{dimH}(f(s)) \le \mathrm{dimH}(s)$.

*Proof sketch.* If $f$ is $K$-Lipschitz, then $\mu_H^d(f(s)) \le K^d \mu_H^d(s)$. So $\mu_H^d(s) = 0$ gives $\mu_H^d(f(s)) = 0$, for each $d > \mathrm{dimH}(s)$.

| Lean name | Statement |
|---|---|
| `HolderOnWith.dimH_image_le` | for a Hölder map of exponent $r > 0$ on $s$, $\mathrm{dimH}(f(s)) \le \mathrm{dimH}(s)/r$ |
| `dimH_image_le_of_locally_lipschitzOn` | the same bound as Lipschitz maps for locally Lipschitz maps, in a second countable space |
| `AntilipschitzWith.le_dimH_image` | an antilipschitz map does not decrease the dimension |
| `Isometry.dimH_image` | an isometry preserves the dimension |
| `ContinuousLinearEquiv.dimH_image` | a continuous linear equivalence preserves the dimension |
| `Real.dimH_of_nonempty_interior` | a set with nonempty interior in a real space of dimension $n$ has dimension $n$ |
| `Real.dimH_univ_eq_finrank` | the whole space of dimension $n$ has dimension $n$ |
| `Real.Convex.dimH_eq_finrank_vectorSpan` | a nonempty convex set has the dimension of its affine span |
| `Differentiable.dimH_range_le` | the range of a differentiable map from a space of dimension $n$ has dimension at most $n$ |

**Proposition** (`dense_compl_of_dimH_lt_finrank`). In a real normed space of finite dimension $n$, a set $s$ with $\mathrm{dimH}(s) < n$ has a dense complement.

*Proof.* Suppose that the complement is not dense. Then $s$ contains a nonempty open set, so $s$ has a nonempty interior, and `Real.dimH_of_nonempty_interior` gives $\mathrm{dimH}(s) = n$. This is a contradiction.

With `Differentiable.dimH_range_le`, this gives `Differentiable.dense_compl_range_of_finrank_lt_finrank`: a differentiable map from a space of smaller dimension has a range with a dense complement. This is an easy form of the theorem of Sard.

The module `Mathlib.Topology.Connected.HausdorffMeasure` relates connected sets and the Hausdorff measures. For a preconnected set $s$ of an extended metric space with a Borel σ-algebra, `IsPreconnected.ediam_le_hausdorffMeasure` gives $\mathrm{diam}(s) \le \mu_H^1(s)$. Thus a connected set with finite $\mu_H^1$ is bounded, and `IsPreconnected.totallyBounded_of_hausdorffMeasure_lt_top` makes it totally bounded. If it is also complete, it is compact by `IsPreconnected.isCompact_of_hausdorffMeasure_lt_top_isComplete`. For $d < 1$, a set with finite $\mu_H^d$ is totally disconnected by `isTotallyDisconnected_of_hausdorffMeasure_lt_top`, so a preconnected set with finite $\mu_H^d$ has at most one point (`IsPreconnected.subsingleton_of_hausdorffMeasure_lt_top`).

#### Common errors

1. The radius of `Metric.IsCover` and of the covering numbers is in `ℝ≥0`, but the radius of `Metric.IsSeparated` is in `ℝ≥0∞`. A statement that mixes them needs a coercion, as in `Metric.IsSeparated (ε : ℝ≥0∞) C`.
2. `Metric.coveringNumber ε A` asks for a cover inside $A$, and it is not monotone in $A$. Use `Metric.externalCoveringNumber_mono_set`, or `Metric.coveringNumber_subset_le` with half the radius.
3. `dimH` is the name of the definition, and it needs an `EMetricSpace`. In a pseudometric space it is not available; pass to the metric quotient first.

### Exercises

1. (A) Show that the covering number of $[0, 1]$ in $\mathbb{R}$ at radius $\varepsilon$ is at most $\lceil 1/(2\varepsilon) \rceil + 1$, with an explicit cover.
2. (A) Use `Metric.IsCover.image_lipschitz` to show that the image of a totally bounded set under a Lipschitz map has finite covering numbers.
3. (A) Show that $\mathbb{Q}$ has Hausdorff dimension $0$ in $\mathbb{R}$ with `dimH_countable`, and deduce that its complement is dense.
4. (B) Show that $\mathrm{pack}(\varepsilon, A) \le \mathrm{cov}(\varepsilon/2, A)$ from the results of this section.
5. (B) Show that the graph of a Lipschitz map $f : \mathbb{R} \to \mathbb{R}$ has Hausdorff dimension $1$ in $\mathbb{R}^2$.
6. (C) Show that a set with covering exponent $d$ has Hausdorff dimension at most $d$, with an estimate of the Hausdorff measure by covers by balls.

### Reference

<?reference?>
