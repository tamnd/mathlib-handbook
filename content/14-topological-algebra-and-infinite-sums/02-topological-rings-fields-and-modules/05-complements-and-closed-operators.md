---
title: Topological complements and closed operators
kind: api
modules:
  - Mathlib.Topology.Algebra.Module.Complement
  - Mathlib.Topology.Algebra.Module.LinearPMap
  - Mathlib.Topology.Algebra.Module.EmbeddingOfLocal
  - Mathlib.Topology.Algebra.Module.Cardinality
  - Mathlib.Topology.Algebra.Module.Compact
  - Mathlib.Topology.Algebra.Module.PerfectSpace
  - Mathlib.Topology.Algebra.Module.Simple
  - Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
explains:
  E2: [Submodule.IsTopCompl, Submodule.ClosedComplemented, Submodule.closedComplemented_iff_exists_isTopCompl, Submodule.projectionL, Submodule.prodEquivOfIsTopCompl, LinearPMap.IsClosed, LinearPMap.IsClosable, LinearPMap.closure, cardinal_eq_of_mem_nhds_zero, LinearMap.isClosed_or_dense_ker]
  E1: auto
families: []
requires: [V07, V13.C01, V13.C04, V14.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Topological complements and closed operators

### Overview

In linear algebra each subspace has a complement: a second subspace $q$ with $p \cap q = 0$ and $p + q = M$. In a topological module this is not enough. The map $p \times q \to M$, $(x, y) \mapsto x + y$, is a continuous bijection, but its inverse need not be continuous. A *topological complement* is a complement for which the inverse is continuous, so that $M$ is the topological direct sum of $p$ and $q$. A closed subspace of a Banach space can fail to have a topological complement, so the notion carries real information.

This section first describes the library of topological complements and continuous projections. It then treats partial linear maps with closed graph, which model unbounded operators. It ends with a group of small results about the cardinality, compactness and density of subsets of topological modules.

### The library around it

#### Topological complements

Let $p$ and $q$ be submodules of a topological module $M$ over a ring $R$. The predicate `Submodule.IsTopCompl p q` says that $p$ and $q$ are complements and that the linear projection onto $p$ along $q$ is continuous. The constructor `Submodule.IsTopCompl.mk` takes a proof of `IsCompl p q` and the continuity of the linear projection `Submodule.projection`. The lemma `Submodule.IsCompl.isTopCompl_iff` states the definition as an equivalence. The relation is symmetric (`Submodule.IsTopCompl.symm` and `Submodule.isTopCompl_comm`), and the projection onto $q$ is $\mathrm{id}$ minus the projection onto $p$.

There are other equivalent forms. For complements $p$ and $q$ in a topological group, the following are equivalent.

1. The projection onto $p$ is continuous.
2. The map $p \times q \to M$ is a homeomorphism (`Submodule.IsCompl.isTopCompl_iff_isHomeomorph_prodEquivOfIsCompl`).
3. The inverse of that map is continuous (`Submodule.IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl`).
4. The linear equivalence $M / p \simeq q$ is continuous (`Submodule.IsCompl.isTopCompl_iff_continuous_quotientEquivOfIsCompl`).

When the conditions hold, the library gives the continuous objects.

| Lean name | Statement |
|---|---|
| `Submodule.projectionL p q h` | the projection $M \to M$ onto $p$ along $q$, as a continuous map |
| `Submodule.projectionOntoL p q h` | the same projection with values in $p$ |
| `Submodule.prodEquivOfIsTopCompl` | the continuous linear equivalence $p \times q \simeq M$ |
| `Submodule.quotientEquivOfIsTopCompl` | the continuous linear equivalence $M / p \simeq q$ |
| `Submodule.projectionL_add_projectionL_eq_id` | the two projections add up to the identity |
| `Submodule.range_projectionL` | the range of the projection onto $p$ is $p$ |
| `Submodule.ker_projectionL` | its kernel is $q$ |
| `ContinuousLinearMap.ofIsTopCompl` | maps on $p$ and on $q$ give one map on $M$ |

The projections and idempotents carry the same information. The lemma `ContinuousLinearMap.isIdempotentElem_iff_eq_projectionL_range_ker` says that a continuous endomorphism $f$ is idempotent if and only if its range and kernel are topological complements and $f$ is the projection onto the range along the kernel. The form `ContinuousLinearMap.IsIdempotentElem.isTopCompl` gives the first half.

A topological complement is closed under a mild condition: $p$ is the kernel of the continuous projection onto $q$, so $p$ is closed when $q$ is $T_1$. The lemma `Submodule.IsTopCompl.isClosed` records the fact. The lemma `Submodule.IsTopCompl.t2Space` says that $p$ is Hausdorff when $q$ is closed.

#### Closed complemented submodules

The predicate `Submodule.ClosedComplemented p` says that there is a continuous linear projection from $M$ onto $p$. The lemma `Submodule.closedComplemented_iff_exists_isTopCompl` says that this holds if and only if $p$ has a topological complement. The complement is the kernel of the projection, and `Submodule.ClosedComplemented.complement` chooses one, with `Submodule.ClosedComplemented.isTopCompl_complement` as its property. A closed complemented submodule of a Hausdorff space is closed (`Submodule.ClosedComplemented.isClosed`).

The basic cases are `Submodule.closedComplemented_bot` and `Submodule.closedComplemented_top`. A map with a one sided inverse gives more: `ContinuousLinearMap.closedComplemented_ker_of_rightInverse` says that the kernel of $f_1$ is closed complemented when $f_1$ has a continuous right inverse $f_2$, and `ContinuousLinearMap.closedComplemented_range_of_leftInverse` gives the range form. Two results in other files cover finite dimension. A finite dimensional subspace of a Hausdorff locally convex space over $\mathbb{R}$ or $\mathbb{C}$ is closed complemented (`Submodule.ClosedComplemented.of_finiteDimensional`). A closed subspace with a finite dimensional quotient is closed complemented (`Submodule.ClosedComplemented.of_finiteDimensional_quotient`).

#### Closed and closable partial maps

A partial linear map `E →ₗ.[R] F` (the type `LinearPMap`) is a linear map from a submodule `LinearPMap.domain f` of $E$ to $F$. Its graph is a submodule of $E \times F$. The module `Mathlib.Topology.Algebra.Module.LinearPMap` gives the topological notions for these maps, the setting of unbounded operators on Hilbert spaces.

1. `LinearPMap.IsClosed f` says that the graph of $f$ is closed in $E \times F$.
2. `LinearPMap.IsClosable f` says that $f$ has a closed extension. By `LinearPMap.isClosable_iff_exists_closed_extension`, this is the same as the existence of a closed $g$ with $f \le g$.
3. `LinearPMap.closure f` is the smallest closed extension when $f$ is closable, and $f$ itself otherwise.
4. `LinearPMap.HasCore f S` says that $S$ is a core: the closure of the restriction of $f$ to $S$ is the closure of $f$.

The main lemma is `LinearPMap.IsClosable.graph_closure_eq_closure_graph`: for a closable $f$, the closure of the graph is the graph of the closure. The lemmas `LinearPMap.le_closure`, `LinearPMap.IsClosable.closure_isClosed` and `LinearPMap.IsClosable.closure_mono` give the order properties. For an injective $f$, the inverse is closed if and only if $f$ is closed (`LinearPMap.inverse_closed_iff`), because the graph of the inverse is the image of the graph under the swap $E \times F \simeq F \times E$. The same argument gives `LinearPMap.inverse_isClosable_iff` and `LinearPMap.inverse_closure`.

#### Topologies fixed by a neighbourhood of zero

The module `Mathlib.Topology.Algebra.Module.EmbeddingOfLocal` proves that the topology of a topological vector space depends only on a neighbourhood of zero. If two group topologies with continuous scalar multiplication induce the same topology on one neighbourhood $V$ of zero, they are equal: this is `ContinuousSMul.topology_eq_of_induced_eq`. A linear map whose restriction to a neighbourhood of zero is an embedding is an embedding (`LinearMap.isEmbedding_of_restrict_nhds_zero`), and the same holds for inducing maps (`LinearMap.isInducing_of_restrict_nhds_zero`).

#### Size, density and compactness

A neighbourhood of zero in a topological vector space over a nontrivially normed field absorbs each vector, so it is as large as the whole space.

| Lean name | Statement |
|---|---|
| `cardinal_eq_of_mem_nhds_zero` | a neighbourhood of $0$ has the cardinality of $E$ |
| `cardinal_eq_of_isOpen` | a nonempty open set has the cardinality of $E$ |
| `continuum_le_cardinal_of_module` | a nontrivial vector space over a complete field has at least $\mathfrak{c}$ elements |
| `continuum_le_cardinal_of_isOpen` | a nonempty open set has at least $\mathfrak{c}$ elements |
| `Set.Countable.dense_compl` | the complement of a countable set is dense |
| `perfectSpace_of_module` | a nontrivial topological vector space has no isolated points |
| `LinearMap.isClosed_or_dense_ker` | the kernel of a map to a simple module is closed or dense |

The last result covers linear functionals: the kernel of a linear functional is a hyperplane, and a hyperplane is closed or dense. Its proof uses that the closure of the kernel is a submodule that contains the kernel, and the kernel is maximal.

The module `Mathlib.Topology.Algebra.Module.Compact` treats modules over a compact ring. A finitely generated submodule is compact (`Submodule.isCompact_of_fg`), because it is the image of $R^n$ under a continuous map. So a finite module over a compact ring is compact (`Module.Finite.compactSpace`), and each ideal of a compact Hausdorff noetherian ring is closed (`IsNoetherianRing.isClosed_ideal`). The ring $\mathbb{Z}_p$ is the main example.

The module `Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear` turns a bilinear map on finite dimensional spaces into a continuous one: `LinearMap.toContinuousBilinearMap` and `IsBilinearMap.toContinuousBilinearMap`.

#### Common errors

1. `IsCompl p q` does not give `Submodule.IsTopCompl p q`. A proof must show that the projection is continuous; in finite dimension the automatic continuity of linear maps does this.
2. `LinearPMap.closure f` is defined for each $f$, but it is the closure only when $f$ is closable. Lemmas such as `LinearPMap.IsClosable.closure_isClosed` need the hypothesis `LinearPMap.IsClosable f`.
3. `Submodule.prodEquivOfIsTopCompl` needs `IsTopologicalAddGroup M` as an instance, but `Submodule.projectionL` does not. A missing instance error at the equivalence often comes from a module with only `ContinuousAdd`.

### Exercises

1. (A) Prove that $\bot$ and $\top$ are topological complements in each topological module, and find the lemma.
2. (A) Use `Set.Countable.dense_compl` to show that $\mathbb{R}^2$ minus the points with rational coordinates is dense.
3. (B) Show that if $f : M \to N$ has a continuous right inverse $g$, then $\ker f$ and the range of $g$ are topological complements.
4. (B) Prove that the graph of a closed partial map is a closed submodule of $E \times F$, and deduce from `LinearPMap.inverse_closed_iff` that the inverse of an injective closed partial map is closed.
5. (C) Give a linear functional on a real vector space with a suitable topology whose kernel is dense, and explain how `LinearMap.isClosed_or_dense_ker` applies.

### Reference

<?reference?>
