---
title: One-sided neighbourhoods, suprema and limit points of orders
kind: api
modules:
  - Mathlib.Topology.Order.LeftRight
  - Mathlib.Topology.Order.LeftRightNhds
  - Mathlib.Topology.Order.DenselyOrdered
  - Mathlib.Topology.Order.IsLUB
  - Mathlib.Topology.Order.ExtendFrom
  - Mathlib.Topology.Order.ProjIcc
  - Mathlib.Topology.Order.Real
  - Mathlib.Topology.Order.SuccPred
  - Mathlib.Topology.Order.WithTop
explains:
  E2: [continuousAt_iff_continuous_left_right, nhdsGT_eq_bot_iff, closure_Ioo, IsLUB.mem_closure, IsClosed.isLUB_mem, exists_seq_tendsto_sSup, IsLUB.isLUB_of_tendsto, SuccOrder.isOpen_singleton_iff, WithTop.tendsto_nhds_top_iff]
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

## One-sided neighbourhoods, suprema and limit points of orders

### Overview

Real analysis often looks at a point from one side. A function has a limit from the left, a derivative from the right, a jump at a point. The library treats these notions with the filters of a point within the rays $(-\infty, a)$, $(-\infty, a]$, $(a, \infty)$ and $[a, \infty)$. This section describes the API of these one-sided filters in a linear order with the order topology: their bases, their join, and the condition that a one-sided filter is trivial.

The second subject is the relation between the order and the closure. A least upper bound of a nonempty set is in its closure, a closed bounded set contains its supremum, and in a densely ordered space the closure of $(a, b)$ is $[a, b]$. The section then treats successor orders, in which a point is isolated unless it is a limit, and the types `WithTop ι` and `WithBot ι` with the order topology. It ends with the extension of functions from an open interval to its closure and with the projection onto a closed interval.

The text uses the classes of Section 1 and the filters `nhdsWithin` of Chapter 2.

### The library around it

#### One-sided filters

The module `Mathlib.Topology.Order.LeftRight` works with a linear order and a topology on it. The filter of $a$ is the join of its two one-sided filters:

$$\mathcal{N}(a) = \mathcal{N}_{(-\infty, a)}(a) \sqcup \mathcal{N}_{[a, \infty)}(a).$$

This is `nhdsLT_sup_nhdsGE`, and `nhdsGE_sup_nhdsLE` and its siblings give the other combinations. The consequence for continuity is `continuousAt_iff_continuous_left_right`: a map is continuous at $a$ if and only if it is continuous at $a$ within $(-\infty, a]$ and within $[a, \infty)$. *Proof.* Continuity at $a$ is the statement that the map sends $\mathcal{N}(a)$ into the filter of $f(a)$. A map of filters respects joins, and the closed half-lines have the same join. The same file gives the forms for `ContinuousWithinAt`, the comparison `continuousWithinAt_Ioi_iff_Ici`, and the fact that the filter of $b$ within $[a, \infty)$ is proper when $a \le b$ (`nhdsWithin_Ici_neBot`). An eventual property near $a$ holds at some point to the right of $a$ when the filter from the right is proper (`Filter.Eventually.exists_gt`). In a space with no isolated point from the left, an antichain has empty interior (`IsAntichain.interior_eq_empty`).

The module `Mathlib.Topology.Order.LeftRightNhds` describes the bases. In the order topology with no maximum, the intervals $(a, u)$ for $u > a$ are a basis of the filter from the right (`nhdsGT_basis`), and `mem_nhdsGT_iff_exists_Ioo_subset` states the membership. The lemma `tfae_mem_nhdsGT` lists five equivalent forms of the statement $s \in \mathcal{N}_{(a, \infty)}(a)$, with intervals cut at a point $b > a$. An order-connected set is a one-sided neighbourhood of each of its points that has a point of the set on that side (`Set.OrdConnected.mem_nhdsGT`).

The filter from the right is trivial exactly when $a$ is a top element or has an immediate successor:

$$\mathcal{N}_{(a, \infty)}(a) = \bot \iff a \text{ is top or } \exists b,\ a \lessdot b.$$

This is `nhdsGT_eq_bot_iff`. *Proof.* If $a \lessdot b$, then $(a, b)$ is empty and it is a set of the filter, so the filter is $\bot$. Conversely, if $a$ is not top and has no successor, each interval $(a, u)$ with $u > a$ is nonempty, so the basis has no empty member. It follows that a second countable order has countably many points that are isolated from the right (`countable_setOfPred_isolated_right`).

For an ordered group the module expresses the neighbourhoods with the absolute value. The sets $\{b : |b - a| < \varepsilon\}$ with $\varepsilon > 0$ are a basis of $\mathcal{N}(a)$ (`nhds_basis_abs_sub_lt`), and `eventually_abs_sub_lt` is the eventual form. The criterion `orderTopology_of_nhds_abs` proves that a topology given by these balls is the order topology. Limits to infinity of sums also live here: if $f$ tends to a constant and $g \to +\infty$, then $f + g \to +\infty$ (`Filter.Tendsto.add_atTop`).

#### Densely ordered spaces

The module `Mathlib.Topology.Order.DenselyOrdered` computes closures, interiors and frontiers of intervals. In a densely ordered space,

$$\overline{(a, b)} = [a, b] \text{ for } a \ne b.$$

This is `closure_Ioo`. *Proof.* The closed interval is closed and contains $(a, b)$, so it contains the closure. For the other inclusion it is enough to put $a$ in the closure. Each neighbourhood of $a$ contains some $[a, u)$ with $u > a$, and by density $[a, u) \cap (a, b)$ is nonempty. The same holds for $b$. The family has a lemma for each kind of interval: `closure_Ioi`, `interior_Icc` (with no minimum and no maximum), `frontier_Ioo`, and the criterion `isClosed_Ioo_iff`, which says that $(a, b)$ is closed only when it is empty. The filters from the left and from the right are proper (`nhdsGT_neBot`). A densely ordered space with the discrete order topology has at most one point (`DenselyOrdered.subsingleton_of_discreteTopology`).

#### Least upper bounds and closures

The module `Mathlib.Topology.Order.IsLUB` relates suprema and closures. If $a$ is a least upper bound of a nonempty set $s$, then $a \in \overline{s}$. This is `IsLUB.mem_closure`. *Proof.* Let $U$ be a neighbourhood of $a$. If $a \in s$ there is nothing to do. If $a \notin s$, then $U$ contains an interval $(c, a]$ with $c < a$. Since $c$ is not an upper bound of $s$, some $x \in s$ satisfies $c < x \le a$, so $x \in U \cap s$. It follows that a closed set contains its least upper bound (`IsClosed.isLUB_mem`), and conversely an upper bound in the closure is the least one (`isLUB_of_mem_closure`). The filter of $a$ within $s$ is proper (`IsLUB.nhdsWithin_neBot`), and points of $s$ come frequently near $a$ from the left (`IsLUB.frequently_mem`).

When the space is first countable, the least upper bound is a limit of a sequence of points of the set. For a nonempty bounded set $S$ there is a monotone sequence of points of $S$ with limit $\sup S$. This is `exists_seq_tendsto_sSup`, and `IsLUB.exists_seq_monotone_tendsto` is the form for a least upper bound. Each point of a densely ordered first countable space with no minimum is the limit of a strictly increasing sequence below it (`exists_seq_strictMono_tendsto`).

A monotone map preserves least upper bounds in the limit: if $f$ is monotone on $s$, $a$ is a least upper bound of $s$ and $f(x) \to b$ as $x \to a$ within $s$, then $b$ is a least upper bound of $f(s)$. This is `IsLUB.isLUB_of_tendsto`, and `IsLUB.mem_upperBounds_of_tendsto` is its first half. A dense subset of an open set has the same least upper bound (`Dense.isLUB_inter_iff`), and for a continuous map the supremum over a dense set is the full supremum (`Dense.ciSup`). For a nonempty closed set bounded below, the upper closure is the ray from its infimum (`upperClosure_eq_Ici_csInf`).

#### Successor orders and isolated points

The module `Mathlib.Topology.Order.SuccPred` treats orders with a successor function, such as $\mathbb{N}$, $\mathbb{Z}$ and the ordinals. In such an order with the order topology, a point is isolated unless it is a limit for the successor:

$$\{a\} \text{ is open} \iff a \text{ is not a successor limit.}$$

This is `SuccOrder.isOpen_singleton_iff`. *Proof.* If $a$ is not a limit, either $a$ is minimal, and then $\{a\} = (-\infty, a]$, or $a$ covers some $b$, and then $\{a\} = (b, a]$. In a successor order each ray $(-\infty, a]$ equals $(-\infty, \mathrm{succ}\,a)$, so it is open (`SuccOrder.isOpen_Iic`), and $(b, a]$ is open too. Conversely, if $a$ is a limit, each interval $(c, a]$ with $c < a$ contains points other than $a$. The criterion `SuccOrder.isOpen_iff` describes all open sets, and `SuccOrder.nhds_eq_pure` gives the filter of an isolated point. The forms for predecessor orders start with `PredOrder`. An accumulation point is always a limit point of the order (`AccPt.isSuccLimit`), and `SuccOrder.accPt_principal` gives the full criterion. For ordinals these facts describe the topology: the successor ordinals are isolated, and a limit ordinal is the limit of the ordinals below it.

#### Adding a top or a bottom

The module `Mathlib.Topology.Order.WithTop` puts the order topology on `WithTop ι` and `WithBot ι` (`TopologicalSpace.instOrderTopologyWithTop`). The coercion is an open embedding (`WithTop.isOpenEmbedding_coe`), and the filter of a coerced point is the image of the filter of the point (`WithTop.nhds_coe`). A map tends to $\top$ if and only if, for each $i$, eventually it is above $i$. This is `WithTop.tendsto_nhds_top_iff`, and it is the order form of the statement $x_n \to \infty$. The points other than $\top$ form a copy of the original space (`WithTop.neTopHomeomorph`), and when the original space has a top, `WithTop.sumHomeomorph` splits off the new point. The module `Mathlib.Topology.Order.Real` gives the topologies of `EReal` and `ENNReal` as order topologies, with their separation instances such as `EReal.instT5Space`. The rationals are dense in the extended reals (`EReal.denseRange_ratCast`).

#### Extension to the closed interval and projection

The module `Mathlib.Topology.Order.ExtendFrom` uses the function `extendFrom` of Chapter 2. Let $f$ be continuous on $(a, b)$, with a limit $\ell_a$ from the right at $a$ and a limit $\ell_b$ from the left at $b$. Then the extension of $f$ to $[a, b]$ by these limits is continuous on $[a, b]$. This is `continuousOn_Icc_extendFrom_Ioo`; it needs a densely ordered source and a regular target.

The module `Mathlib.Topology.Order.ProjIcc` treats the projection `Set.projIcc a b h` of the line onto $[a, b]$, which sends each point to the nearest point of the interval. It is continuous (`continuous_projIcc`) and it is a quotient map (`isQuotientMap_projIcc`). The extension `Set.IccExtend h f` of a map on the interval is continuous if and only if the map is continuous (`continuous_IccExtend_iff`). Paths in Chapter 6 use this extension to view a map on $[0, 1]$ as a map on $\mathbb{R}$.

#### Common errors

1. The basis `nhdsGT_basis` needs `NoMaxOrder`. At a point with an immediate successor, the filter from the right is $\bot$, and a statement that asks for a proper filter fails there. Check the class with `nhdsGT_eq_bot_iff` in mind.
2. The lemma `closure_Ioo` asks for $a \ne b$. For $a = b$ the open interval is empty, but the closed interval `Set.Icc a a` is $\{a\}$, so the equation is false.
3. The lemma `IsLUB.mem_closure` needs a nonempty set. The empty set has the bottom element as least upper bound, and this point need not be in the closure of the empty set.

### Exercises

1. (A) Prove that $\overline{(0, 1)} = [0, 1]$ in $\mathbb{R}$ with `closure_Ioo`, and compute the frontier of $(0, 1)$.
2. (A) Use `continuousAt_iff_continuous_left_right` to prove that the map $x \mapsto |x|$ is continuous at 0 from its two one-sided restrictions.
3. (B) Show that in $\mathbb{N}$ with the order topology each singleton is open, and deduce that the topology is discrete.
4. (B) Let $S \subseteq \mathbb{R}$ be nonempty and bounded above. Prove that there is a monotone sequence of points of $S$ that tends to $\sup S$, first by hand and then with `exists_seq_tendsto_sSup`.
5. (B) Prove that $\omega$, the first infinite ordinal, is not isolated in the ordinals below $\omega + 1$, and that each finite ordinal is isolated.
6. (C) Let $f$ be monotone on a set $s$ with least upper bound $a$, and let $f(x) \to b$ as $x \to a$ within $s$. Prove that $b$ is the least upper bound of $f(s)$, as in `IsLUB.isLUB_of_tendsto`.

### Reference

<?reference?>
