---
title: Metrizable spaces and partitions of unity
kind: api
modules:
  - Mathlib.Topology.Metrizable.Basic
  - Mathlib.Topology.Metrizable.Uniformity
  - Mathlib.Topology.Metrizable.Urysohn
  - Mathlib.Topology.Metrizable.CompletelyMetrizable
  - Mathlib.Topology.Metrizable.ContinuousMap
  - Mathlib.Topology.Metrizable.Real
  - Mathlib.Topology.ShrinkingLemma
  - Mathlib.Topology.PartitionOfUnity
explains:
  E2: [TopologicalSpace.MetrizableSpace, TopologicalSpace.PseudoMetrizableSpace, UniformSpace.metrizable_uniformity, PseudoMetricSpace.le_two_mul_dist_ofPreNNDist, TopologicalSpace.metrizableSpace_of_t3_secondCountable, TopologicalSpace.IsCompletelyMetrizableSpace, exists_iUnion_eq_closure_subset, PartitionOfUnity, BumpCovering.toPartitionOfUnity, PartitionOfUnity.exists_isSubordinate]
  E1: auto
families: []
requires: [V13.C03, V13.C04, V13.C05, V13.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Metrizable spaces and partitions of unity

### Overview

A topological space is metrizable if some metric induces its topology. Many spaces of analysis are metrizable, but no metric is part of their data: a subspace, a countable product, the space of continuous maps on a $\sigma$-compact space. The library treats metrizability as a property of a topology, with a class that asserts the existence of a compatible metric. A proof can then choose such a metric when it needs one. This section describes this class and the two metrization theorems of the library: a uniform space with a countable basis of entourages is pseudometrizable, and a regular second countable space is metrizable. The second theorem uses the lemma of Urysohn from Section 1.

The second part of the section treats two results on normal spaces that go with the lemma of Urysohn: the shrinking lemma and the existence of partitions of unity. A partition of unity subordinate to an open cover is the standard tool to glue local constructions into a global one, in topology, in analysis and on manifolds.

### The library around it

#### The classes of metrizable spaces

The module `Mathlib.Topology.Metrizable.Basic` defines two classes in the namespace `TopologicalSpace`. The class `TopologicalSpace.PseudoMetrizableSpace X` says that some pseudometric induces the topology of $X$. The class `TopologicalSpace.MetrizableSpace X` adds the $T_0$ axiom, `TopologicalSpace.MetrizableSpace.toT0Space`. A pseudometric with the $T_0$ property is a metric, so this is the same as the existence of a compatible metric. Conversely, `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace` builds the class from a pseudometrizable $T_0$ space.

The function `TopologicalSpace.pseudoMetrizableSpaceUniformity X` chooses a compatible uniformity, and `TopologicalSpace.pseudoMetrizableSpacePseudoMetric X` and `TopologicalSpace.metrizableSpaceMetric X` choose a compatible pseudometric or metric. These are definitions, not instances. A proof uses them with the tactic letI when it needs a metric, and the result does not depend on the choice.

The classes have the expected consequences and constructions.

| Lean name | Statement |
|---|---|
| `TopologicalSpace.t2Space_of_metrizableSpace` | a metrizable space is Hausdorff |
| `TopologicalSpace.PseudoMetrizableSpace.regularSpace` | a pseudometrizable space is regular |
| `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology` | a pseudometrizable space is first countable |
| `TopologicalSpace.MetrizableSpace.subtype` | a subspace of a metrizable space is metrizable |
| `TopologicalSpace.metrizableSpace_prod` | a product of two metrizable spaces is metrizable |
| `TopologicalSpace.metrizableSpace_pi` | a finite product of metrizable spaces is metrizable |
| `Topology.IsEmbedding.metrizableSpace` | a space that embeds in a metrizable space is metrizable |
| `IsCompact.isSeparable` | a compact set in a pseudometrizable space is separable |

The instance `TopologicalSpace.DiscreteTopology.metrizableSpace` covers discrete spaces. The modules `Mathlib.Topology.Metrizable.Real` and `Mathlib.Topology.Metrizable.ContinuousMap` add the instances `ENNReal.instMetrizableSpace` and `ContinuousMap.instMetrizableSpace`. The second one says that `C(X, Y)` is metrizable when $X$ is weakly locally compact and $\sigma$-compact and $Y$ is metrizable. The proof shows that the uniformity of compact convergence of Chapter 7 has a countable basis, built from a compact exhaustion of $X$, and then applies the metrization of uniform spaces below.

#### Metrization of uniform spaces

A pseudometric space has the countable basis of entourages $\{d < 1/n\}$. The converse is `UniformSpace.metrizable_uniformity`: a uniformity with a countably generated filter of entourages comes from a pseudometric. The definitions `UniformSpace.pseudoMetricSpace X` and `UniformSpace.metricSpace X` give the metric, and `UniformSpace.metrizableSpace` is the instance for the topology. So `UniformSpace.pseudoMetrizableSpace` makes each such uniform space pseudometrizable.

The proof is in `Mathlib.Topology.Metrizable.Uniformity`, and it has a general core. Let $d$ be a symmetric function to $\mathbb{R}_{\ge 0}$ with $d(x, x) = 0$. The definition `PseudoMetricSpace.ofPreNNDist d` is the largest pseudometric below $d$: the distance is the infimum of $\sum_i d(x_i, x_{i+1})$ over all chains from $x$ to $y$. So `PseudoMetricSpace.dist_ofPreNNDist_le` says $\mathrm{dist}(x, y) \le d(x, y)$. The key estimate goes the other way. If $d$ satisfies the weak triangle inequality

$$d(x_1, x_4) \le 2 \max(d(x_1, x_2), d(x_2, x_3), d(x_3, x_4)),$$

then $d(x, y) \le 2\,\mathrm{dist}(x, y)$, by `PseudoMetricSpace.le_two_mul_dist_ofPreNNDist`. The proof is an induction on the length of the chain: it splits the chain at the point where the partial sums pass half of the total. For a uniform space, take a decreasing sequence of symmetric entourages $U_n$ with $U_{n+1} \circ U_{n+1} \circ U_{n+1} \subseteq U_n$, and let $d(x, y) = 2^{-n}$ for the largest $n$ with $(x, y) \in U_n$. This $d$ satisfies the weak triangle inequality, and the pseudometric `PseudoMetricSpace.ofPreNNDist d` induces the uniformity.

An extended metric space has the countable basis $\{\mathrm{edist} < 1/n\}$, so `EMetricSpace.metrizableSpace` and `PseudoEMetricSpace.pseudoMetrizableSpace` hold.

#### The Urysohn metrization theorem

The module `Mathlib.Topology.Metrizable.Urysohn` proves the metrization theorem of Urysohn: a regular second countable space is pseudometrizable, `TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology`, and a $T_3$ second countable space is metrizable, `TopologicalSpace.metrizableSpace_of_t3_secondCountable`. The proof embeds the space in the Banach space $\ell^\infty$ of bounded real sequences, `TopologicalSpace.exists_embedding_l_infty`. A regular second countable space is normal. Take a countable basis $B$. For each pair $(U, V)$ of basic sets with $\overline{U} \subseteq V$, the lemma of Urysohn gives a function $f_{U,V}$ that is $1$ on $\overline{U}$ and $0$ outside $V$. Enumerate the pairs and scale the $n$-th function by a factor that tends to $0$. The resulting map to $\ell^\infty$ is continuous, and the functions separate points from closed sets, so it is an embedding.

#### Completely metrizable spaces

The module `Mathlib.Topology.Metrizable.CompletelyMetrizable` defines `TopologicalSpace.IsCompletelyMetrizableSpace X`: some complete metric induces the topology, by `TopologicalSpace.IsCompletelyMetrizableSpace.complete`. The pseudometric form is `TopologicalSpace.IsCompletelyPseudoMetrizableSpace`. These are the spaces where the Baire theorem of Chapter 3 holds. A complete metric space is one, `MetricSpace.toIsCompletelyMetrizableSpace`. A closed subset is one, `IsClosed.isCompletelyMetrizableSpace`, and so is a countable product, `TopologicalSpace.IsCompletelyMetrizableSpace.pi_countable`, a finite product and a sum. The function `TopologicalSpace.completelyMetrizableMetric X` chooses a complete metric, with `TopologicalSpace.complete_completelyMetrizableMetric`. The class `TopologicalSpace.UpgradedIsCompletelyMetrizableSpace` bundles a chosen complete metric for the cases where a proof needs it as an instance, and `TopologicalSpace.upgradeIsCompletelyMetrizable` builds it.

#### The shrinking lemma

The module `Mathlib.Topology.ShrinkingLemma` proves the shrinking lemma. Let $X$ be normal, and let $(U_i)$ be a point-finite open cover: each point is in finitely many $U_i$. Then there is an open cover $(V_i)$ with $\overline{V_i} \subseteq U_i$ for each $i$. This is `exists_iUnion_eq_closure_subset`, with the form for a closed subset `exists_subset_iUnion_closure_subset` and the forms with closed sets `exists_iUnion_eq_closed_subset`. The proof uses the lemma of Zorn on partial refinements, the structures `ShrinkingLemma.PartialRefinement`. A partial refinement has replaced $U_i$ by $V_i$ for $i$ in a set of indices, `ShrinkingLemma.PartialRefinement.carrier`, and still covers. The order is extension. A chain has an upper bound, `ShrinkingLemma.PartialRefinement.chainSup`, and here the point-finiteness is used. A maximal element has all indices: if $i$ is missing, the closed set of points that only $U_i$ covers has an open neighbourhood $V_i$ with $\overline{V_i} \subseteq U_i$, by normality, and this extends the refinement, `ShrinkingLemma.PartialRefinement.exists_gt`. The module also has a form for compact sets in a Hausdorff space, `exists_subset_iUnion_compact_subset_t2space`.

#### Partitions of unity

The module `Mathlib.Topology.PartitionOfUnity` defines `PartitionOfUnity ι X s`: a family of continuous functions $\rho_i : X \to \mathbb{R}$ with locally finite supports, $\rho_i \ge 0$, $\sum_i \rho_i(x) = 1$ for $x \in s$ and $\sum_i \rho_i \le 1$ everywhere. The fields are `PartitionOfUnity.locallyFinite`, `PartitionOfUnity.nonneg`, `PartitionOfUnity.sum_eq_one` and `PartitionOfUnity.sum_le_one`. The sums are `finsum`, and they make sense because only finitely many $\rho_i(x)$ are nonzero. Near each point, finitely many functions carry the whole sum: `PartitionOfUnity.finsupport` gives this finite set of indices, and `PartitionOfUnity.sum_finsupport` gives the sum over it. A partition is subordinate to a family $(U_i)$, `PartitionOfUnity.IsSubordinate`, if the closed support of $\rho_i$ lies in $U_i$.

The library builds a partition of unity from a bump covering, `BumpCovering ι X s`. A bump covering is a locally finite family of continuous functions $f_i : X \to [0, 1]$ such that each point of $s$ has a neighbourhood on which some $f_i$ is $1$. Fix a well-order on $\iota$. Then `BumpCovering.toPartitionOfUnity` sets

$$\rho_i(x) = f_i(x) \prod_{j < i} (1 - f_j(x)),$$

by `BumpCovering.toPartitionOfUnity_eq_mul_prod`. The sum telescopes: $\sum_i \rho_i = 1 - \prod_i (1 - f_i)$, and the product vanishes on $s$ because some factor is $0$. This is `BumpCovering.sum_toPartitionOfUnity_eq`.

Existence uses the lemma of Urysohn and the shrinking lemma. For a locally finite open cover of a closed set in a normal space, shrink the cover twice and apply Urysohn to each pair, `BumpCovering.exists_isSubordinate_of_locallyFinite`. In a paracompact normal space each open cover has a locally finite refinement, so `PartitionOfUnity.exists_isSubordinate` gives a partition of unity subordinate to any open cover of a closed set. In a locally compact Hausdorff space there is a form with compact supports, `PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space`, and `exists_continuous_sum_one_of_isOpen_isCompact` treats a finite cover of a compact set. The main application is the gluing lemma `PartitionOfUnity.IsSubordinate.continuous_finsum_smul`: if $g_i$ is continuous on $U_i$, then $\sum_i \rho_i g_i$ is continuous on $X$.

#### Common errors

1. `TopologicalSpace.metrizableSpaceMetric X` is a definition, not an instance. To use a metric on a metrizable space, introduce it with the tactic letI. Do not add an instance of `MetricSpace X` to a type that already has a topology, or there are two topologies on $X$.
2. A countably generated uniformity gives a pseudometric with the same uniformity, not only the same topology. A metrizable topology gives a metric with the same topology only, and its uniformity can differ from a uniformity already on the type.
3. The functions of a partition of unity are summed with `finsum`, not with `tsum`. A lemma about `tsum` does not apply to `PartitionOfUnity.sum_eq_one`.

### Exercises

1. (A) Prove that a subspace of a metrizable space is metrizable, and that a metrizable space is Hausdorff.
2. (A) Show that the discrete topology on any type is metrizable, with the metric that is $1$ on distinct points.
3. (B) For a bump covering $(f_i)$ indexed by a finite well-ordered set, prove that $\sum_i f_i \prod_{j < i} (1 - f_j) = 1 - \prod_i (1 - f_i)$.
4. (B) Prove the shrinking lemma for a finite open cover of a normal space, by induction on the number of sets.
5. (B) Let $(\rho_i)$ be a partition of unity subordinate to an open cover $(U_i)$, and let $g_i : X \to \mathbb{R}$ be continuous on $U_i$. Prove that $\sum_i \rho_i g_i$ is continuous on $X$.
6. (C) Prove the metrization theorem of Urysohn: a $T_3$ second countable space embeds in $\ell^\infty$.

### Reference

<?reference?>
