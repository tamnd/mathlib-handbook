---
title: Extended metric spaces
kind: api
modules:
  - Mathlib.Topology.EMetricSpace.Basic
  - Mathlib.Topology.EMetricSpace.Diam
  - Mathlib.Topology.EMetricSpace.Pi
  - Mathlib.Topology.EMetricSpace.MulOpposite
  - Mathlib.Topology.EMetricSpace.Paracompact
  - Mathlib.Topology.EMetricSpace.Weak
  - Mathlib.Topology.MetricSpace.PartitionOfUnity
  - Mathlib.Topology.MetricSpace.ShrinkingLemma
explains:
  E2: ["EMetric.cauchySeq_iff'", EMetric.inseparable_iff, Metric.ediam_le_iff, Metric.ediam_pair, Metric.ediam_eball_le, Metric.ediam_union_le_add_edist, edist_pi_le_iff, ENNReal.edist_eq_max, Option.ball_infty_of_pos]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Extended metric spaces

### Overview

An extended metric takes values in $[0, \infty]$, the type `ENNReal` of Mathlib. Section 1 introduced the classes `PseudoEMetricSpace` and `EMetricSpace` and the distance `EDist.edist`. They are needed for spaces where two points can be at infinite distance: the space of all functions $\alpha \to \mathbb{R}$ with the sup distance, a disjoint union of metric spaces, or the space of measurable sets with the measure of the symmetric difference. In Mathlib each `PseudoMetricSpace` is also a `PseudoEMetricSpace`, with $\mathrm{edist}(x, y) = d(x, y)$ as an element of $[0, \infty]$, so each lemma of this section applies to metric spaces as well.

This section describes the general lemmas of extended metric spaces: Cauchy sequences, total boundedness, countability and the Lebesgue number lemma. It then treats the extended diameter `Metric.ediam`, the sup distance on finite products, the paracompactness of extended metric spaces and two consequences in metric spaces, the shrinking lemma and a continuous choice of radii. It ends with the weak extended metric spaces, a recent class whose main examples are $[0, \infty]$ itself and the extended reals.

### The library around it

#### Cauchy sequences, separation and countability

The module `Mathlib.Topology.EMetricSpace.Basic` gives the $\varepsilon$ forms of the uniform notions in the namespace EMetric. The lemma `EMetric.cauchySeq_iff'` states that a sequence $u$ indexed by a nonempty join semilattice is Cauchy if and only if
$$\forall \varepsilon > 0,\ \exists N,\ \forall n \ge N,\ \mathrm{edist}(u_n, u_N) < \varepsilon.$$
Proof: if $u$ is Cauchy, the uniformity basis of the sets $\{\mathrm{edist} < \varepsilon\}$ gives $N$ with $\mathrm{edist}(u_m, u_n) < \varepsilon$ for $m, n \ge N$, and $m = N$ is a special case. Conversely, the condition for $\varepsilon/2$ and the triangle inequality give $\mathrm{edist}(u_m, u_n) \le \mathrm{edist}(u_m, u_N) + \mathrm{edist}(u_N, u_n) < \varepsilon$ for $m, n \ge N$. The variant `EMetric.cauchySeq_iff` has the two indices, `EMetric.cauchySeq_iff_NNReal` asks only for $\varepsilon$ in $[0, \infty)$, and `EMetric.cauchy_iff` is the form for filters.

Two lemmas prove completeness from sequences. `EMetric.complete_of_cauchySeq_tendsto` says that a space where each Cauchy sequence converges is complete. `EMetric.complete_of_convergent_controlled_sequences` asks only for the convergence of the sequences with $\mathrm{edist}(u_n, u_m) < B_N$ for $n, m \ge N$, for a fixed sequence of positive bounds $B$.

The separation lemmas have the same form as in Section 3. The lemma `EMetric.inseparable_iff` states that $x$ and $y$ are inseparable if and only if $\mathrm{edist}(x, y) = 0$. Proof: if $\mathrm{edist}(x, y) = 0$, the triangle inequality gives the same balls around $x$ and $y$; if $\mathrm{edist}(x, y) = r > 0$, the ball of radius $r$ around $x$ does not contain $y$. Then `EMetricSpace.ofT0PseudoEMetricSpace` turns a $T_0$ pseudo extended metric space into an extended metric space, and `instEMetricSpaceSeparationQuotient` puts an extended metric on the quotient by the relation $\mathrm{edist}(x, y) = 0$, with formula `SeparationQuotient.edist_mk`.

Total boundedness is stated with finite nets: `EMetric.totallyBounded_iff` and `EMetric.totallyBounded_iff'` (with the centres in the set). For countability, `EMetric.secondCountable_of_almost_dense_set` gives second countability from countable $\varepsilon$-dense sets, and `EMetric.secondCountable_of_sigmaCompact` says that a $\sigma$-compact pseudo extended metric space is second countable. A compact set has a countable dense subset: `EMetric.countable_closure_of_compact`. The Lebesgue number lemma has several forms: `lebesgue_number_lemma_of_emetric` for an open cover, `lebesgue_number_lemma_of_emetric_sUnion` for a family of sets, and `lebesgue_number_lemma_of_emetric_nhds` and `lebesgue_number_lemma_of_emetric_nhdsWithin` for a choice of one neighbourhood at each point.

The module also has the telescoping bounds `edist_le_range_sum_edist` and `edist_le_Ico_sum_edist`, the $\varepsilon$ forms of uniform convergence such as `EMetric.tendstoUniformly_iff`, and the product instance `Prod.emetricSpaceMax`.

#### The extended diameter

The module `Mathlib.Topology.EMetricSpace.Diam` defines `Metric.ediam s`, the supremum of $\mathrm{edist}(x, y)$ over $x, y \in s$, with value in $[0, \infty]$. The definition needs only an `EDist` instance; the lemmas that use the triangle inequality need a weak pseudo extended metric (see the last part). The formula is `Metric.ediam_eq_sSup`. The main lemma is `Metric.ediam_le_iff`:
$$\mathrm{ediam}(s) \le d \iff \forall x, y \in s,\ \mathrm{edist}(x, y) \le d.$$
Proof: this is the definition of a supremum. The two halves are `Metric.ediam_le` and `Metric.edist_le_of_ediam_le`, and `Metric.edist_le_ediam_of_mem` is the case $d = \mathrm{ediam}(s)$.

| Lean name | Statement |
|---|---|
| `Metric.ediam_empty` | $\mathrm{ediam}(\emptyset) = 0$ |
| `Metric.ediam_singleton` | $\mathrm{ediam}(\{x\}) = 0$ |
| `Metric.ediam_pair` | $\mathrm{ediam}(\{x, y\}) = \mathrm{edist}(x, y)$ |
| `Metric.ediam_triple` | the diameter of $\{x, y, z\}$ is the max of the three distances |
| `Metric.ediam_insert` | $\mathrm{ediam}(\{x\} \cup s) = \max(\sup_{y \in s} \mathrm{edist}(x, y), \mathrm{ediam}(s))$ |
| `Metric.ediam_mono` | $s \subseteq t \Rightarrow \mathrm{ediam}(s) \le \mathrm{ediam}(t)$ |
| `Metric.ediam_eq_zero_iff` | in an extended metric space, $\mathrm{ediam}(s) = 0$ iff $s$ has at most one point |
| `Metric.ediam_pos_iff` | $0 < \mathrm{ediam}(s)$ iff $s$ has two distinct points |
| `Metric.ediam_eball_le` | $\mathrm{ediam}(B(x, r)) \le 2r$ |
| `Metric.ediam_closedEBall_le` | the same bound for the closed ball |
| `Metric.ediam_pi_le_of_le` | a product of sets of diameter at most $c$ has diameter at most $c$ |

Two proofs show the method. For `Metric.ediam_pair`, the pairs of points of $\{x, y\}$ have distances $0$, $\mathrm{edist}(x, y)$ and $\mathrm{edist}(y, x) = \mathrm{edist}(x, y)$, and the largest is $\mathrm{edist}(x, y)$. For `Metric.ediam_eball_le`, take $y, z \in B(x, r)$; then $\mathrm{edist}(y, z) \le \mathrm{edist}(y, x) + \mathrm{edist}(x, z) \le 2r$, and `Metric.ediam_le` concludes.

The union of two sets has a bound with a bridge between them. The lemma `Metric.ediam_union_le_add_edist` states: for $x \in s$ and $y \in t$,
$$\mathrm{ediam}(s \cup t) \le \mathrm{ediam}(s) + \mathrm{edist}(x, y) + \mathrm{ediam}(t).$$
Proof: two points in the same set satisfy the bound already. For $a \in s$ and $b \in t$, the triangle inequality through $x$ and $y$ gives $\mathrm{edist}(a, b) \le \mathrm{edist}(a, x) + \mathrm{edist}(x, y) + \mathrm{edist}(y, b)$, and each term is bounded by the matching term on the right. When the two sets meet, `Metric.ediam_union_le` gives the bound $\mathrm{ediam}(s) + \mathrm{ediam}(t)$.

The real diameter `Metric.diam` of Chapter 5 is the real number attached to `Metric.ediam`. It is $0$ for an unbounded set, so the lemmas on `Metric.diam` often need a boundedness hypothesis that the lemmas on `Metric.ediam` do not need.

#### Products and opposites

The instance `pseudoEMetricSpacePi` on a finite product uses the sup distance, with the formula `edist_pi_def`. Its main lemma is `edist_pi_le_iff`: $\mathrm{edist}(f, g) \le d \iff \forall b,\ \mathrm{edist}(f_b, g_b) \le d$. Proof: the distance is the sup over a finite set, and a sup is at most $d$ exactly when each term is. In contrast with the real form `dist_pi_le_iff` of Section 3, no sign condition on $d$ is needed, because $d \ge 0$ holds in $[0, \infty]$. The family has `edist_le_pi_edist`, `edist_pi_const` and the instance `emetricSpacePi`.

The module `Mathlib.Topology.EMetricSpace.MulOpposite` copies the structure to the opposite types: `MulOpposite.instPseudoEMetricSpace` and `AddOpposite.instPseudoEMetricSpace`, with the simp lemmas `MulOpposite.edist_op` and `MulOpposite.edist_unop`.

#### Paracompactness and its consequences

The module `Mathlib.Topology.EMetricSpace.Paracompact` proves the theorem of Stone in the extended metric case: each pseudo extended metric space is paracompact (`Metric.instParacompactSpace`). With the Hausdorff property this gives normality, so each extended metric space is $T_4$ (`Metric.t4Space`). The proof is long and the section does not reproduce it.

Two modules use this. The module `Mathlib.Topology.MetricSpace.PartitionOfUnity` proves `Metric.exists_continuous_real_forall_closedBall_subset`: let $K_i$ be a locally finite family of closed sets of a metric space and $U_i \supseteq K_i$ open sets. Then there is a continuous function $\delta : X \to (0, \infty)$ with $\bar B(x, \delta(x)) \subseteq U_i$ for each $i$ and each $x \in K_i$. A single radius cannot work in general, since $K_i$ can come close to the boundary of $U_i$; the function $\delta$ adapts to the point. The family has the forms with values in `NNReal` and `ENNReal`, and the extended metric forms such as `Metric.exists_continuous_nnreal_forall_closedEBall_subset`.

The module `Mathlib.Topology.MetricSpace.ShrinkingLemma` proves the shrinking lemma for balls in a proper metric space. The lemma `exists_iUnion_ball_eq_radius_lt` states: if the balls $B(c_i, r_i)$ cover the space and each point is in finitely many of them, then there are radii $r'_i < r_i$ such that the balls $B(c_i, r'_i)$ still cover the space. The form `exists_subset_iUnion_ball_radius_lt` covers a closed set, and `exists_locallyFinite_iUnion_eq_ball_radius_lt` builds a locally finite cover by balls with radii below a given positive function $R$.

#### Weak extended metric spaces

The extended distance $\mathrm{edist}(a, b) = |a - b|$ on $[0, \infty]$, with $\mathrm{edist}(a, \infty) = \infty$ for finite $a$, does not give the usual topology: in the distance topology the point $\infty$ is isolated, but in the order topology each neighbourhood of $\infty$ contains real numbers. So `ENNReal` is not a `PseudoEMetricSpace` in Mathlib. The class `WeakPseudoEMetricSpace` covers this case. It asks for an extended distance with the three axioms on a type that already has a topology, such that each open set of the topology is open for the distance, and each ball $B(x, r)$ is open in the subspace of points at finite distance from $x$. The class `WeakEMetricSpace` adds that distance $0$ forces equality.

The module `Mathlib.Topology.EMetricSpace.Weak` gives the instances `instWeakEMetricSpaceENNReal`, `instWeakEMetricSpaceEReal` and `instWeakEMetricSpaceENat`. They come from one construction: the distance `Option.toEDist` on `Option α` extends the distance of $\alpha$ by $\mathrm{edist}(\mathrm{none}, a) = \infty$ for $a \ne \mathrm{none}$ (`Option.edist_none_some`). When the inclusion of $\alpha$ is an open embedding, as for `WithTop.isOpenEmbedding_some`, this gives a weak structure: `Option.WeakEMetricSpace.OfIsOpenEmbedding`, and the instances on `WithTop`, `WithBot` and `OnePoint`. The lemma `Option.ball_infty_of_pos` states that for $r > 0$ the ball of radius $r$ around $\mathrm{none}$ is $\{\mathrm{none}\}$. Proof: each other point is at distance $\infty$, and $\infty < r$ is false.

For `ENNReal` the module gives a list of formulas. The lemma `ENNReal.edist_eq_max` states $\mathrm{edist}(a, b) = \max(a - b, b - a)$ with truncated subtraction. Proof: for finite $a \ge b$ the max is $a - b = |a - b|$; if one of them is $\infty$ and the other is finite, both sides are $\infty$; if both are $\infty$, both sides are $0$. The other lemmas follow from it: `ENNReal.edist_zero_right` ($\mathrm{edist}(a, 0) = a$), `ENNReal.edist_eq_top_iff`, `ENNReal.edist_coe` (on `NNReal` the distance is the usual one), `ENNReal.edist_add_left` and `ENNReal.edist_mul_left` (for $c \ne \infty$), and `ENNReal.edist_le_iff_le_add_right`.

#### Common errors

1. `Metric.ediam` and `Metric.diam` differ on unbounded sets: the first is $\infty$, the second is $0$. A bound on `Metric.diam` without a boundedness hypothesis is often false or useless.
2. `ENNReal` has an `EDist` instance and a `WeakEMetricSpace` instance, but no `PseudoEMetricSpace` instance. A lemma stated for `PseudoEMetricSpace` does not apply to it; look for the form with `WeakPseudoEMetricSpace`.
3. The extended balls `Metric.eball` and `Metric.closedEBall` and the diameter `Metric.ediam` are in the namespace Metric, while the Cauchy, completeness and countability lemmas of this section are in the namespace EMetric. Search both namespaces.

### Exercises

1. (A) Show that $\mathrm{ediam}(\{x, y, z\})$ is the max of the three distances, and compare with `Metric.ediam_triple`.
2. (A) Use `Metric.ediam_le_iff` to show that an isometry $f$ satisfies $\mathrm{ediam}(f(s)) = \mathrm{ediam}(s)$.
3. (B) Show that the sup distance on the functions $\mathbb{N} \to \mathbb{R}$ is an extended metric, and that its topology is not the product topology.
4. (B) Prove `ENNReal.edist_le_iff_le_add_right` from `ENNReal.edist_eq_max`.
5. (B) Show that in $[0, \infty]$ with the distance topology the set $\{\infty\}$ is open, and that it is not open in the order topology.
6. (C) Let $X$ be a proper metric space and $B(c_i, r_i)$ a point-finite cover by open balls. Show directly, without `exists_iUnion_ball_eq_radius_lt`, that one ball can be shrunk while the family still covers $X$.

### Reference

<?reference?>
