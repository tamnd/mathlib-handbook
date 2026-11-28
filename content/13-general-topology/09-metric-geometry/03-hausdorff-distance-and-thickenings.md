---
title: The Hausdorff distance and thickenings
kind: api
modules:
  - Mathlib.Topology.MetricSpace.HausdorffDistance
  - Mathlib.Topology.MetricSpace.Thickening
  - Mathlib.Topology.MetricSpace.ThickenedIndicator
  - Mathlib.Topology.MetricSpace.Closeds
  - Mathlib.Topology.MetricSpace.Infsep
explains:
  E2: [Metric.infEDist_le_infEDist_add_edist, Metric.mem_closure_iff_infEDist_zero, Metric.hausdorffEDist_triangle, Metric.hausdorffEDist_zero_iff_closure_eq_closure, Metric.closure_eq_iInter_thickening, IsCompact.exists_thickening_subset_open, lipschitzWith_thickenedIndicator, TopologicalSpace.Closeds.isometry_singleton, Set.einfsep_pair]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C03, V13.C05, V13.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Hausdorff distance and thickenings

### Overview

A metric gives a distance between points. Many arguments need a distance between a point and a set, or between two sets. The distance from $x$ to a set $s$ is $\inf_{y \in s} d(x, y)$. It is $0$ exactly when $x$ is in the closure of $s$. The Hausdorff distance between two sets $s$ and $t$ is the least $r$ such that each point of $s$ is within $r$ of $t$ and each point of $t$ is within $r$ of $s$. It makes the closed sets of a metric space into a metric space of its own.

The five modules of this section hold this library. `Mathlib.Topology.MetricSpace.HausdorffDistance` defines the distance from a point to a set and the Hausdorff distance. `Mathlib.Topology.MetricSpace.Thickening` defines the open and closed $\delta$-neighbourhoods of a set. `Mathlib.Topology.MetricSpace.ThickenedIndicator` builds continuous functions that approximate the indicator function of a closed set. `Mathlib.Topology.MetricSpace.Closeds` puts the Hausdorff metric on the types of closed sets and compact sets. `Mathlib.Topology.MetricSpace.Infsep` defines the least distance between distinct points of a set. The section uses metric spaces (Chapter 3), compactness (Chapter 5) and uniform spaces (Chapter 7).

### The library around it

#### The distance from a point to a set

All definitions start in a pseudo extended metric space, with values in $[0, \infty]$. The function `Metric.infEDist x s` is $\inf_{y \in s} \operatorname{edist}(x, y)$. It is $\infty$ for $s = \emptyset$ (`Metric.infEDist_empty`). In a pseudometric space, `Metric.infDist x s` is the real number obtained from it. Its value on the empty set is $0$, so lemmas about `Metric.infDist` often ask for a proof that $s$ is nonempty.

The basic facts are lattice facts. The distance is antitone in the set (`Metric.infEDist_anti`), it turns unions into minima (`Metric.infEDist_union`, `Metric.infEDist_iUnion`), and it does not see closures (`Metric.infEDist_closure`). The point estimate `Metric.infEDist_le_edist_of_mem` says $\operatorname{infEDist}(x, s) \le \operatorname{edist}(x, y)$ for $y \in s$. The key inequality is `Metric.infEDist_le_infEDist_add_edist`:
$$\operatorname{infEDist}(x, s) \le \operatorname{infEDist}(y, s) + \operatorname{edist}(x, y).$$
Proof: for each $z \in s$, $\operatorname{infEDist}(x, s) \le \operatorname{edist}(x, z) \le \operatorname{edist}(y, z) + \operatorname{edist}(x, y)$, and the infimum over $z$ gives the claim. So $x \mapsto \operatorname{infDist}(x, s)$ is $1$-Lipschitz (`Metric.lipschitz_infDist_pt`) and continuous (`Metric.continuous_infEDist`).

The distance detects the closure: `Metric.mem_closure_iff_infEDist_zero` says $x \in \overline{s}$ if and only if $\operatorname{infEDist}(x, s) = 0$. Both sides say that each ball around $x$ meets $s$. For a closed set this gives `IsClosed.mem_iff_infDist_zero`, and outside the closure the distance is positive: `Metric.infDist_pos_iff_notMem_closure`. The infimum is attained on compact sets (`IsCompact.exists_infDist_eq_dist`), and on closed sets of a proper space (`IsClosed.exists_infDist_eq_dist`).

One consequence is a classical fact of metric topology: each open set $U$ is an increasing union of closed sets, `IsOpen.exists_iUnion_isClosed`. The proof takes $F_n = \{x : \operatorname{infEDist}(x, U^c) \ge a^n\}$ for a number $0 < a < 1$. Each $F_n$ is closed by continuity, and each point of $U$ has a positive distance to the closed set $U^c$.

#### The Hausdorff distance

The function `Metric.hausdorffEDist s t` is the larger of $\sup_{x \in s} \operatorname{infEDist}(x, t)$ and $\sup_{y \in t} \operatorname{infEDist}(y, s)$. The real form `Metric.hausdorffDist s t` is obtained from it, with the value $0$ when the extended distance is $\infty$. The extended distance is finite for two nonempty bounded sets (`Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded`), and many lemmas about `Metric.hausdorffDist` ask for the hypothesis `Metric.hausdorffEDist s t ≠ ⊤`.

| Lean name | Statement |
|---|---|
| `Metric.hausdorffEDist_self` | $d_H(s, s) = 0$ |
| `Metric.hausdorffEDist_comm` | $d_H(s, t) = d_H(t, s)$ |
| `Metric.hausdorffEDist_triangle` | $d_H(s, u) \le d_H(s, t) + d_H(t, u)$ |
| `Metric.hausdorffEDist_closure` | $d_H(\overline{s}, \overline{t}) = d_H(s, t)$ |
| `Metric.hausdorffEDist_zero_iff_closure_eq_closure` | $d_H(s, t) = 0 \iff \overline{s} = \overline{t}$ |
| `Metric.infEDist_le_hausdorffEDist_of_mem` | $x \in s \Rightarrow \operatorname{infEDist}(x, t) \le d_H(s, t)$ |
| `Metric.hausdorffEDist_le_of_mem_edist` | if each point of one set is within $r$ of the other set, both ways, then $d_H(s, t) \le r$ |
| `Metric.hausdorffEDist_image` | an isometry keeps $d_H$ |
| `Metric.hausdorffEDist_le_ediam` | $d_H(s, t) \le \operatorname{diam}(s \cup t)$ for nonempty sets |

The triangle inequality follows from the point version. For $x \in s$ the lemma `Metric.infEDist_le_infEDist_add_hausdorffEDist` gives $\operatorname{infEDist}(x, u) \le \operatorname{infEDist}(x, t) + d_H(t, u) \le d_H(s, t) + d_H(t, u)$. The same bound holds for the points of $u$, and the supremum gives the claim. The zero criterion follows from `Metric.mem_closure_iff_infEDist_zero`: $d_H(s, t) = 0$ says that each point of $s$ is in $\overline{t}$ and each point of $t$ is in $\overline{s}$. So on closed sets the Hausdorff distance separates points (`IsClosed.hausdorffEDist_zero_iff`). The real forms carry the same names with hausdorffDist in place of hausdorffEDist, for example `Metric.hausdorffDist_triangle` and `Metric.exists_dist_lt_of_hausdorffDist_lt`.

#### Thickenings

The open thickening `Metric.thickening δ E` is $\{x : \operatorname{infEDist}(x, E) < \delta\}$, and the closed thickening `Metric.cthickening δ E` is $\{x : \operatorname{infEDist}(x, E) \le \delta\}$ (`Metric.thickening_eq_preimage_infEDist`, `Metric.cthickening_eq_preimage_infEDist`). The radius is a real number. The open thickening is empty for $\delta \le 0$ (`Metric.thickening_of_nonpos`), and the closed thickening with radius $0$ is the closure (`Metric.cthickening_zero`). The membership lemmas are `Metric.mem_thickening_iff`, which says that some point of $E$ is at distance less than $\delta$, and `Metric.mem_cthickening_iff`.

The open thickening is open (`Metric.isOpen_thickening`) and is the union of the open balls $B(x, \delta)$ with $x \in E$ (`Metric.thickening_eq_biUnion_ball`). The closed thickening is closed (`Metric.isClosed_cthickening`), but it can be larger than the union of the closed balls. The two agree for a compact set (`IsCompact.cthickening_eq_biUnion_closedBall`), and in a proper space for the closure of a set (`Metric.cthickening_eq_biUnion_closedBall`). A thickening of a singleton is a ball (`Metric.thickening_singleton`, `Metric.cthickening_singleton`), and thickenings add: `Metric.thickening_thickening_subset` states $(E_\delta)_\varepsilon \subseteq E_{\varepsilon + \delta}$. Thickening keeps boundedness (`Bornology.IsBounded.thickening`), and in a proper space it keeps compactness (`IsCompact.cthickening`).

The closure is the intersection of the thickenings: `Metric.closure_eq_iInter_thickening` states
$$\overline{E} = \bigcap_{\delta > 0} E_\delta.$$
A point is in each $E_\delta$ exactly when $\operatorname{infEDist}(x, E) < \delta$ for each $\delta > 0$, that is, when $\operatorname{infEDist}(x, E) = 0$. The criterion for the closure then gives the claim. The closed form is `Metric.closure_eq_iInter_cthickening`.

Around a compact set the thickenings form a basis of neighbourhoods. The lemma `IsCompact.exists_thickening_subset_open` says: if $K$ is compact, $U$ is open and $K \subseteq U$, then $K_\delta \subseteq U$ for some $\delta > 0$. Proof: the function $x \mapsto \operatorname{infDist}(x, U^c)$ is continuous and positive on $K$, so it has a positive minimum $\delta$ on $K$, and then $K_\delta \subseteq U$. The filter form is `Metric.hasBasis_nhdsSet_thickening`, and `Disjoint.exists_thickenings` separates a compact set and a disjoint closed set by disjoint thickenings.

#### Thickened indicators

Let $E$ be a set and $\delta > 0$. The function `thickenedIndicator δ_pos E` is the bounded continuous function $x \mapsto \max(0, 1 - \operatorname{infEDist}(x, E) / \delta)$ with values in $\mathbb{R}_{\ge 0}$. The same formula with values in $[0, \infty]$ is `thickenedIndicatorAux`. The function is $1$ on the closure of $E$ (`thickenedIndicator_one_of_mem_closure`), $0$ outside $E_\delta$ (`thickenedIndicator_zero`) and at most $1$ everywhere (`thickenedIndicator_le_one`). It is Lipschitz with constant $\delta^{-1}$ (`lipschitzWith_thickenedIndicator`), because it is the composition of the $1$-Lipschitz map $x \mapsto \operatorname{infEDist}(x, E)$ with a function of slope $\delta^{-1}$. When $\delta_n \to 0$, the functions converge pointwise to the indicator of $\overline{E}$ (`thickenedIndicator_tendsto_indicator_closure`). These functions are the metric form of the lemma of Urysohn of Chapter 8, with an explicit formula. They appear in measure theory, where they approximate closed sets by continuous functions.

The module also proves the convergence of indicators of thickenings themselves: `tendsto_indicator_thickening_indicator_closure` states that $\mathbf{1}_{E_\delta} f \to \mathbf{1}_{\overline{E}} f$ pointwise as $\delta \to 0^+$.

#### The spaces of closed and compact sets

The module `Mathlib.Topology.MetricSpace.Closeds` uses the Hausdorff distance as a metric on sets. The structure `PseudoEMetricSpace.hausdorff` puts the Hausdorff extended pseudometric on `Set α`. It is not an instance. On the closed sets of an extended metric space the Hausdorff distance separates points, so `TopologicalSpace.Closeds α` is an extended metric space (`TopologicalSpace.Closeds.instEMetricSpace`), with `TopologicalSpace.Closeds.edist_eq` as the defining equation. The same holds for the compact sets, `TopologicalSpace.Compacts.instEMetricSpace`. On the nonempty compact sets of a metric space the distance is finite, and `TopologicalSpace.NonemptyCompacts.instMetricSpace` gives a metric space with `TopologicalSpace.NonemptyCompacts.dist_eq`.

The main theorem of the module is completeness: `TopologicalSpace.Closeds.instCompleteSpace` says that the closed sets of a complete space form a complete space. The proof takes a sequence $s_n$ with $d_H(s_n, s_{n+1}) < 2^{-n}$, shows that it converges to $\bigcap_n \overline{\bigcup_{m \ge n} s_m}$, and applies the criterion for completeness by fast Cauchy sequences. The embeddings into these spaces are isometries.

| Lean name | Statement |
|---|---|
| `TopologicalSpace.Closeds.isometry_singleton` | $x \mapsto \{x\}$ is an isometry into the closed sets |
| `TopologicalSpace.NonemptyCompacts.isometry_toCloseds` | the inclusion of nonempty compacts into closed sets |
| `TopologicalSpace.Closeds.lipschitz_sup` | $(s, t) \mapsto s \cup t$ is $1$-Lipschitz |
| `TopologicalSpace.Closeds.lipschitz_prod` | $(s, t) \mapsto s \times t$ is $1$-Lipschitz |
| `TopologicalSpace.NonemptyCompacts.lipschitz_infDist` | $(x, K) \mapsto \operatorname{infDist}(x, K)$ is $2$-Lipschitz |

The first entry has a one line proof: $\operatorname{infEDist}(x, \{y\}) = \operatorname{edist}(x, y)$, so $d_H(\{x\}, \{y\}) = \operatorname{edist}(x, y)$.

#### The separation of a set

The module `Mathlib.Topology.MetricSpace.Infsep` defines the dual of the diameter. The function `Set.einfsep s` is the infimum of $\operatorname{edist}(x, y)$ over distinct $x, y \in s$, and `Set.infsep s` is its real form, with value $0$ when the extended value is $0$ or $\infty$ (`Set.infsep_zero`). The names are in the namespace `Set`, so that a proof can use dot notation on a set.

The extended separation is $\infty$ exactly for a subsingleton (`Set.einfsep_eq_top_iff`). For two distinct points it is their distance: `Set.einfsep_pair` states $\operatorname{einfsep}\{x, y\} = \operatorname{edist}(x, y)$, because $(x, y)$ and $(y, x)$ are the only pairs of distinct points. For three points `Set.einfsep_triple` gives the least of the three distances. The characterization `Set.le_einfsep_iff` says $d \le \operatorname{einfsep}(s)$ if and only if $d \le \operatorname{edist}(x, y)$ for all distinct $x, y \in s$. A finite set in an extended metric space has positive separation (`Set.Finite.einfsep_pos`), and a finite nontrivial set attains it at some pair (`Set.Nontrivial.infsep_exists_of_finite`). The form `Set.Finite.relatively_discrete` says that the points of a finite set are uniformly apart.

#### Common errors

1. `Metric.infDist x ∅ = 0` and `Metric.hausdorffDist s ∅ = 0`, while the extended forms give $\infty$ when $s$ is nonempty (`Metric.infEDist_empty`, `Metric.hausdorffEDist_empty`). A lemma about the real forms often needs a nonempty set or the hypothesis `Metric.hausdorffEDist s t ≠ ⊤`, and the real form of the triangle inequality has this hypothesis.
2. The closed thickening is defined by $\operatorname{infEDist}(x, E) \le \delta$, not as a union of closed balls. The two sets differ in general, and the equality needs compactness or a proper space.
3. The metric on closed sets is not an instance on `Set α`. A proof uses the types `TopologicalSpace.Closeds α` or `TopologicalSpace.NonemptyCompacts α`, or the explicit structure `PseudoEMetricSpace.hausdorff`.

### Exercises

1. (A) Compute the Hausdorff distance between $[0, 1]$ and $[0, 2]$ in $\mathbb{R}$, and between $[0, 1]$ and $\{0, 1\}$.
2. (A) Show that $\operatorname{infDist}(x, s) = \operatorname{infDist}(x, \overline{s})$ with the lemmas of the section.
3. (B) Prove that a closed set $F$ in a metric space is a $G_\delta$ set, with `Metric.closure_eq_iInter_thickening`.
4. (B) Give two closed sets of $\mathbb{R}^2$ that are disjoint but have distance $0$, and explain why `Disjoint.exists_thickenings` needs a compact set.
5. (B) Show that $d_H(\overline{s}, \{x\}) \le r$ if and only if $s \subseteq \bar{B}(x, r)$, for a nonempty set $s$.
6. (C) Prove that the set of finite subsets is dense in the space of nonempty compact subsets of a metric space.

### Reference

<?reference?>
