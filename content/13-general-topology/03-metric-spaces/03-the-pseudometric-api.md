---
title: The pseudometric API
kind: api
modules:
  - Mathlib.Topology.MetricSpace.Pseudo.Basic
  - Mathlib.Topology.MetricSpace.Pseudo.Lemmas
  - Mathlib.Topology.MetricSpace.Pseudo.Pi
  - Mathlib.Topology.MetricSpace.Pseudo.Real
  - Mathlib.Topology.MetricSpace.Basic
  - Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
  - Mathlib.Topology.MetricSpace.ProperSpace.Real
  - Mathlib.Topology.MetricSpace.Sequences
  - Mathlib.Topology.MetricSpace.CauSeqFilter
  - Mathlib.Topology.MetricSpace.TransferInstance
  - Mathlib.Topology.MetricSpace.Completion
  - Mathlib.Topology.MetricSpace.BundledFun
explains:
  E2: [MetricSpace.ofT0PseudoMetricSpace, Metric.inseparable_iff, Metric.isClosed_of_pairwise_le_dist, dist_le_range_sum_dist, Metric.secondCountable_of_almost_dense_set, dist_pi_lt_iff, PseudoMetric.IsUltra.sup]
  E1: auto
families: []
requires: [V02, V04, V13.C01, V13.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The pseudometric API

### Overview

Section 1 defines the classes `PseudoMetricSpace` and `MetricSpace`, the balls and the metric topology. A student who uses these classes in a proof soon needs more: the closed balls are closed, a telescoping bound on a sequence, the $\varepsilon$ forms of uniform convergence, the sup distance on a finite product, and the metric on a completion. This section describes the modules that hold this everyday library.

The modules fall into four groups. The first group gives the general lemmas on balls, Cauchy filters, total boundedness and uniform convergence in a pseudometric space. The second group builds metric spaces: from a pseudometric space with the $T_0$ property, from an embedding, from an equivalence of types, on finite products and on a completion. The third group treats proper spaces and the real line. The last module defines pseudometrics as bundled functions, so that the pseudometrics on one type form an ordered set.

### The library around it

#### Balls, closures and limits

The module `Mathlib.Topology.MetricSpace.Pseudo.Lemmas` holds the facts about balls that need the topology. A closed ball is closed (`Metric.isClosed_closedBall`), and so is a sphere (`Metric.isClosed_sphere`). The closure of an open ball is inside the closed ball of the same radius (`Metric.closure_ball_subset_closedBall`). The inclusion can be strict: in a discrete space with the metric $d(x, y) = 1$ for $x \ne y$, the ball $B(x, 1)$ is $\{x\}$ and is closed, but $\bar B(x, 1)$ is the whole space. The frontier of a ball is inside the sphere (`Metric.frontier_ball_subset_sphere`, `Metric.frontier_closedBall_subset_sphere`).

Two lemmas describe balls by limits of radii: $\bigcup_{r' < r} B(x, r') = B(x, r)$ (`Metric.biUnion_lt_ball`) and $\bigcap_{r' > r} \bar B(x, r') = \bar B(x, r)$ (`Metric.biInter_gt_closedBall`). In a pseudometric space the closed ball of radius $0$ is the closure of the point, $\bar B(x, 0) = \overline{\{x\}}$ (`Metric.closedBall_zero'`). The lemmas `eventually_ball_subset` and `eventually_closedBall_subset` say that a neighbourhood $u$ of $x$ contains $B(x, r)$ for all small $r$, as an eventual statement for the filter $\mathcal{N}(0)$ on the radius.

The squeeze lemma `squeeze_zero` states: if $0 \le f(t) \le g(t)$ for all $t$ and $g \to 0$ along a filter, then $f \to 0$. The form `squeeze_zero'` asks for the two inequalities only eventually. These two lemmas are the usual way to prove that a distance tends to $0$. The same module also proves the Lebesgue number lemma `lebesgue_number_lemma_of_metric`, which Chapter 5 uses, and gives the instance `instOrderTopologyReal`: the metric topology on $\mathbb{R}$ is the order topology.

#### Inseparable points and the passage to a metric

In a pseudometric space two different points can have distance $0$. The lemma `Metric.inseparable_iff` states that $x$ and $y$ are inseparable (they have the same neighbourhoods) if and only if $d(x, y) = 0$. Proof: if $d(x, y) = 0$, then $B(x, r) = B(y, r)$ for each $r$ by the triangle inequality, so $x$ and $y$ have the same basis of neighbourhoods. If $d(x, y) = r > 0$, then $y \notin B(x, r)$, so the neighbourhood $B(x, r)$ of $x$ does not contain $y$. The lemmas `dist_congr_left`, `dist_congr_right` and `dist_congr` then replace a point by an inseparable point inside a distance.

Two constructions give a metric space. The definition `MetricSpace.ofT0PseudoMetricSpace` makes a metric space from a pseudometric space with the $T_0$ property. Proof: if $d(x, y) = 0$, then $x$ and $y$ are inseparable by `Metric.inseparable_iff`, and the $T_0$ property says that inseparable points are equal. The instance `SeparationQuotient.instMetricSpace` puts a metric on the quotient by the relation $d(x, y) = 0$, with `SeparationQuotient.dist_mk` as its formula. Conversely each metric space is $T_0$ (`MetricSpace.instT0Space`).

#### Building metric structures

The module `Mathlib.Topology.MetricSpace.Basic` gives the standard instances: `Real.metricSpace`, `instMetricSpaceNNReal`, `Subtype.metricSpace`, `Prod.metricSpaceMax`, `metricSpacePi`, `MulOpposite.instMetricSpace` and `instMetricSpaceULift`. It also gives the tools to make a new structure from an old one.

| Lean name | Statement |
|---|---|
| `MetricSpace.induced` | an injective map $f : \gamma \to \beta$ pulls back a metric on $\beta$ to $\gamma$ |
| `Topology.IsEmbedding.comapMetricSpace` | the same, with the given topology of $\gamma$ kept |
| `IsUniformEmbedding.comapMetricSpace` | the same, with the given uniformity of $\gamma$ kept |
| `MetricSpace.replaceDist` | replace the distance field by a function equal to it |
| `EMetricSpace.toMetricSpace` | an extended metric space with finite distances is a metric space |
| `Equiv.metricSpace` | an equivalence $\alpha \simeq \beta$ moves a metric from $\beta$ to $\alpha$ |
| `Equiv.pseudometricSpace` | the same for a pseudometric |

The last two rows come from `Mathlib.Topology.MetricSpace.TransferInstance`, with `Equiv.dist` for the distance alone. The "comap" forms exist because of the forgetful inheritance of Section 1: when $\gamma$ already has a topology, the induced metric must carry that topology as a field, or the type has two topologies that are equal only by a theorem.

A set whose points are uniformly far apart is closed. The lemma `Metric.isClosed_of_pairwise_le_dist` states: if $\varepsilon > 0$ and $d(x, y) \ge \varepsilon$ for all distinct $x, y \in s$, then $s$ is closed. Proof: let $x \in \bar s$. The ball $B(x, \varepsilon/2)$ contains at most one point of $s$, since two such points have distance less than $\varepsilon$. It contains at least one point $y$, since $x \in \bar s$. If $y \ne x$, then the ball of radius $\min(\varepsilon/2, d(x, y))$ around $x$ misses $s$, which contradicts $x \in \bar s$. So $x = y \in s$. The companions `Metric.isClosedEmbedding_of_pairwise_le_dist` and `Metric.isUniformEmbedding_bot_of_pairwise_le_dist` say that such a family is a closed embedding of a discrete space.

#### Cauchy filters, total boundedness and uniform convergence

The module `Mathlib.Topology.MetricSpace.Pseudo.Basic` translates the notions of uniform spaces (Chapter 7) into distances. The lemma `Metric.cauchy_iff` states that a filter is Cauchy if and only if it is proper and contains sets of arbitrarily small diameter. The lemma `cauchySeq_iff_tendsto_dist_atTop_0` says that $u$ is Cauchy if and only if $d(u_m, u_n) \to 0$ as $(m, n) \to \infty$. The lemmas `Metric.isUniformInducing_iff` and `Metric.isUniformEmbedding_iff` give the $\varepsilon$-$\delta$ form of a uniform embedding: $f$ is uniformly continuous, and small distances of $f(a), f(b)$ force small distances of $a, b$.

The four forms of uniform convergence have the expected $\varepsilon$ statements: `Metric.tendstoUniformly_iff`, `Metric.tendstoUniformlyOn_iff`, `Metric.tendstoLocallyUniformly_iff` and `Metric.tendstoLocallyUniformlyOn_iff`. For instance $F_n \to f$ uniformly if and only if for each $\varepsilon > 0$, eventually $d(f(x), F_n(x)) < \varepsilon$ for all $x$.

The telescoping bounds control the distance between two terms of a sequence by the steps between them. The lemma `dist_le_range_sum_dist` states
$$d(f(0), f(n)) \le \sum_{i < n} d(f(i), f(i+1)).$$
Proof: by induction on $n$. The case $n = 0$ is $d(f(0), f(0)) = 0$. For the step, the triangle inequality gives $d(f(0), f(n+1)) \le d(f(0), f(n)) + d(f(n), f(n+1))$, and the induction hypothesis bounds the first term. The forms `dist_le_Ico_sum_dist` (for $m \le n$ and a sum over $[m, n)$) and `dist_le_range_sum_of_dist_le` (with given bounds $d_k$ on the steps) are the ones used to prove that a sequence with summable steps is Cauchy.

For compactness and countability the module gives `Metric.finite_approx_of_totallyBounded`, `IsCompact.finite_cover_balls` (a compact set is covered by finitely many $\varepsilon$-balls with centres in the set) and `Metric.secondCountable_of_almost_dense_set`. The last one states: if for each $\varepsilon > 0$ there is a countable set $s$ with each point at distance at most $\varepsilon$ from $s$, then the space is second countable. Proof sketch: take such sets $s_n$ for $\varepsilon = 1/n$. Their union $D$ is countable and dense. The balls $B(y, 1/m)$ with $y \in D$ and $m \ge 1$ form a countable basis: if $x \in U$ open with $B(x, 2/m) \subseteq U$, choose $y \in D$ with $d(x, y) < 1/m$, then $x \in B(y, 1/m) \subseteq U$.

#### Finite products

The instance `pseudoMetricSpacePi` on a finite product $\prod_b X_b$ uses the sup distance, $d(f, g) = \sup_b d(f_b, g_b)$, written as a `Finset.sup` of the non-negative distances in `dist_pi_def`. The family of lemmas in `Mathlib.Topology.MetricSpace.Pseudo.Pi` describes it.

| Lean name | Statement |
|---|---|
| `dist_le_pi_dist` | $d(f_b, g_b) \le d(f, g)$ |
| `dist_pi_le_iff` | for $r \ge 0$: $d(f, g) \le r \iff \forall b,\ d(f_b, g_b) \le r$ |
| `dist_pi_lt_iff` | for $r > 0$: $d(f, g) < r \iff \forall b,\ d(f_b, g_b) < r$ |
| `ball_pi` | for $r > 0$: $B(x, r) = \prod_b B(x_b, r)$ |
| `closedBall_pi` | for $r \ge 0$: $\bar B(x, r) = \prod_b \bar B(x_b, r)$ |
| `dist_pi_const` | the distance of two constant functions, for a nonempty index type |
| `dist_single_single` | $d(\delta_i a, \delta_j b) = \max(d(a, 0), d(b, 0))$ for $i \ne j$ |
| `Fin.dist_insertNth_insertNth` | the distance of two tuples with one inserted coordinate |

The hypothesis $r > 0$ in `dist_pi_lt_iff` is needed. The sup over a finite set of nonnegative reals is less than $r$ if and only if each term is less than $r$ and $0 < r$: the sup of the empty family is $0$, and $0 < r$ fails for $r \le 0$. The primed forms `dist_pi_le_iff'` and `ball_pi'` remove the sign condition when the index type is nonempty. Each lemma has a twin for the non-negative distance, such as `nnDist_pi_le_iff`.

#### The real line, proper spaces and sequences

The module `Mathlib.Topology.MetricSpace.Pseudo.Real` bounds distances inside intervals: `Real.dist_le_of_mem_Icc` says $|x - y| \le y' - x'$ for $x, y \in [x', y']$, with the unordered form `Real.dist_le_of_mem_uIcc` and the cube form `Real.dist_le_of_mem_pi_Icc`. The module `Mathlib.Topology.MetricSpace.ProperSpace.Real` gives the instances `NNReal.instProperSpace` and the second countability of `NNReal`, `ENNReal` and `EReal`.

In a proper space the function $y \mapsto d(x, y)$ is a proper map (`isProperMap_dist`), and the lemma `properSpace_iff_isProperMap_dist` turns this into a characterization. A closed set inside an open ball lies in a smaller ball (`exists_lt_subset_ball`, `exists_pos_lt_subset_ball`). The lemma `Metric.exists_isLocalMin_mem_ball` gives a local minimum inside a ball for a continuous function that is smaller at one point of the closed ball than on the whole sphere.

The module `Mathlib.Topology.MetricSpace.Sequences` holds the Bolzano-Weierstrass theorem for proper spaces: `tendsto_subseq_of_bounded` gives a convergent subsequence of a sequence in a bounded set, with limit in its closure. The form `tendsto_subseq_of_frequently_bounded` needs the sequence in the set only frequently.

#### Cauchy sequences of the algebra library and completions

Algebra defines Cauchy sequences with an absolute value, in the structure `CauSeq`, to construct $\mathbb{R}$ (Volume 2). The module `Mathlib.Topology.MetricSpace.CauSeqFilter` connects them with the filter notion: `isCauSeq_iff_cauchySeq` says that the two notions agree in a normed field, `CauSeq.tendsto_limit` says that a `CauSeq` tends to its limit, and `completeSpace_of_cauSeq_isComplete` turns completeness for `CauSeq` into `CompleteSpace`.

The module `Mathlib.Topology.MetricSpace.Completion` puts a metric on the completion of Chapter 7. The instance `UniformSpace.Completion.instMetricSpace` is the extension of the distance by continuity, and `UniformSpace.Completion.dist_eq` says that it agrees with the distance of $\alpha$ on the image of $\alpha$. Then `UniformSpace.Completion.coe_isometry` states that the inclusion is an isometry. Maps extend with their constants: `LipschitzWith.completion_map`, `LipschitzWith.completion_extension`, `Isometry.completion_map` and `Isometry.completion_extension`. For an isometric ring homomorphism, `UniformSpace.Completion.isometry_mapRingHom` says that the induced ring homomorphism of completions is again an isometry.

#### Bundled pseudometrics

The module `Mathlib.Topology.MetricSpace.BundledFun` defines a structure `PseudoMetric X R`: a function $d : X \to X \to R$ with $d(x, x) = 0$, symmetry and the triangle inequality. It is not a class. Many pseudometrics on one type can then live side by side, which is the situation of a family of seminorms. The coercion to a function comes from `PseudoMetric.instFunLikeForall`, and the axioms are `PseudoMetric.refl`, `PseudoMetric.symm` and `PseudoMetric.triangle`. Nonnegativity, `PseudoMetric.nonneg`, is a theorem and needs a strictly monotone addition on $R$.

The pseudometrics form a partial order by pointwise comparison (`PseudoMetric.coe_le_coe`), with least element the zero function (`PseudoMetric.bot_apply`) and the pointwise maximum as sup (`PseudoMetric.sup_apply`, `PseudoMetric.coe_finsetSup`). The class `PseudoMetric.IsUltra` asks for the strong triangle inequality $d(x, z) \le \max(d(x, y), d(y, z))$. It is kept by sups: `PseudoMetric.IsUltra.sup`. Proof: $d(x, z) \le d(x, y) \sqcup d(y, z) \le (d \sqcup d')(x, y) \sqcup (d \sqcup d')(y, z)$, and the same bound holds for $d'(x, z)$, so it holds for their max. For an ultrametric, the strict and the closed balls give transitive relations (`PseudoMetric.IsUltra.isTrans_ball`).

#### Common errors

1. `dist_pi_lt_iff` and `ball_pi` need $0 < r$. With an empty index type the product is one point at distance $0$ from itself, and $0 < r$ is then not automatic. Use the primed forms when the index type is nonempty.
2. A metric built with `MetricSpace.induced` on a type that already has a topology gives a second topology. Use `Topology.IsEmbedding.comapMetricSpace` or `IsUniformEmbedding.comapMetricSpace` so that the instance keeps the given structure by definition.
3. The non-negative distance is `NNDist.nnDist`, and the lemmas follow the name: `nnDist_pi_le_iff`, `nnDist_congr`. Older code writes the lowercase form, which is now only a deprecated alias.

### Exercises

1. (A) Show that $\bar B(x, 0) = \{x\}$ in a metric space, and compare with `Metric.closedBall_zero'`.
2. (A) Use `dist_le_range_sum_of_dist_le` to show that if $d(u_k, u_{k+1}) \le 2^{-k}$ for all $k$, then $d(u_0, u_n) \le 2$ for all $n$.
3. (A) Show that for $r > 0$ the ball $B(x, r)$ in a finite product with the sup distance is the product of the balls $B(x_b, r)$.
4. (B) Give a metric space and a point $x$ with $\overline{B(x, 1)} \ne \bar B(x, 1)$, and a pseudometric space with $\bar B(x, 0) \ne \{x\}$.
5. (B) Show that a separable pseudometric space is second countable, with `Metric.secondCountable_of_almost_dense_set`.
6. (C) Let $(d_n)$ be a sequence of pseudometrics on $X$ with values in $[0, 1]$. Show that $\sum_n 2^{-n} d_n$ is a pseudometric. Show with an example that the sum of two ultrametrics need not be an ultrametric, while their max is one by `PseudoMetric.IsUltra.sup`.

### Reference

<?reference?>
