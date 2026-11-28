---
title: Locally connected and totally disconnected spaces
kind: api
modules:
  - Mathlib.Topology.Connected.LocallyConnected
  - Mathlib.Topology.Connected.TotallyDisconnected
  - Mathlib.Topology.Connected.Separation
  - Mathlib.Topology.Connected.CardComponents
  - Mathlib.Topology.Clopen
  - Mathlib.Topology.ClopenBox
explains:
  E2: [locallyConnectedSpace_iff_connected_subsets, isOpen_connectedComponent, instDiscreteTopologyConnectedComponentsOfLocallyConnectedSpace, totallyDisconnectedSpace_iff_connectedComponent_singleton, Continuous.connectedComponentsLift, totallySeparatedSpace_iff_exists_isClopen, isClopen_iff_frontier_eq_empty, TopologicalSpace.Clopens.exists_finset_eq_sup_prod, IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Locally connected and totally disconnected spaces

### Overview

Section 1 splits a space into its connected components. This section studies the two extreme cases. In a *locally connected* space, each point has a basis of connected neighborhoods. Then the components are open, and the space is the disjoint sum of its components. In a *totally disconnected* space, each component is a single point. The rational numbers, the Cantor set and the $p$-adic integers are examples.

Between the two cases is the quotient `ConnectedComponents X`, whose points are the components of $X$. This quotient is always totally disconnected. It is discrete when $X$ is locally connected, and it is finite when $X$ is also compact.

A stronger condition than total disconnectedness is *total separation*: each two distinct points are separated by a clopen set. A totally separated space is totally disconnected and Hausdorff. For compact Hausdorff spaces the two conditions agree, and these spaces are the profinite spaces of Volume 27.

The section also describes the API of clopen sets. The definition `IsClopen` and the criterion `isClopen_iff` are in Section 1. Here are the closure rules, the clopen sets of products, and the count of components under open and closed maps.

The section uses connected sets and components from Section 1, the separation axioms of Chapter 4 and compactness of Chapter 5.

### The library around it

#### Clopen sets

The module `Mathlib.Topology.Clopen` gives the closure rules for the predicate `IsClopen s`, which is `IsClosed s ∧ IsOpen s`:

- `isClopen_empty`, `isClopen_univ` and `isClopen_discrete` for the basic examples;
- `IsClopen.union`, `IsClopen.inter`, `IsClopen.compl`, `IsClopen.diff` and `IsClopen.himp` for the Boolean operations;
- `isClopen_iUnion_of_finite`, `isClopen_iInter_of_finite`, `Set.Finite.isClopen_biUnion` and `isClopen_biInter_finset` for finite unions and intersections;
- `IsClopen.preimage` for a continuous map, `ContinuousOn.preimage_isClopen_of_isClopen` for a map continuous on a clopen set, and `Topology.IsQuotientMap.isClopen_preimage` for a quotient map;
- `IsClopen.prod` for products, and `isClopen_range_inl`, `isClopen_range_inr` and `isClopen_range_sigmaMk` for the pieces of a sum.

Two criteria are used often. The criterion `isClopen_iff_frontier_eq_empty` says that a set is clopen if and only if its frontier is empty. The criterion `isClopen_of_disjoint_cover_open` says that if two disjoint open sets cover the space, then each of them is clopen. The indicator form `continuous_boolIndicator_iff_isClopen` says that the indicator function of $s$ with Boolean values is continuous if and only if $s$ is clopen.

The bundled type `TopologicalSpace.Clopens X` is a Boolean algebra. The module `Mathlib.Topology.ClopenBox` studies the clopen sets of a product. If $Y$ is compact, `TopologicalSpace.Clopens.exists_prod_subset` gives, for each point of a clopen set $W$ of $X \times Y$, a clopen box $U \times V$ around the point inside $W$. If both factors are compact, `TopologicalSpace.Clopens.exists_finset_eq_sup_prod` writes $W$ as a finite union of clopen boxes. The instances `TopologicalSpace.Clopens.finite_prod` and `TopologicalSpace.Clopens.countable_prod` follow. For a compact Hausdorff totally disconnected space, `TopologicalSpace.Clopens.countable_iff_secondCountable` says that the space has countably many clopen sets if and only if it is second countable.

#### Locally connected spaces

The module `Mathlib.Topology.Connected.LocallyConnected` defines the class `LocallyConnectedSpace X`. Its field `LocallyConnectedSpace.open_connected_basis` says that each point has a basis of open connected neighborhoods. The equivalent forms are:

- `locallyConnectedSpace_iff_hasBasis_isOpen_isConnected`, which uses `Filter.HasBasis`;
- `locallyConnectedSpace_iff_connected_subsets`: each neighborhood $U$ of $x$ contains a preconnected neighborhood of $x$;
- `locallyConnectedSpace_iff_connectedComponentIn_open`: for each open set $F$, the components of $F$ are open;
- `locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected`: the open preconnected sets form a basis.

The main consequences are `isOpen_connectedComponent`, which says that the components of a locally connected space are open, and `connectedComponentIn_mem_nhds`, which says that the component of $x$ in a neighborhood $F$ of $x$ is again a neighborhood of $x$. Thus `instDiscreteTopologyConnectedComponentsOfLocallyConnectedSpace` makes the space of components discrete. With compactness, `instFiniteConnectedComponentsOfLocallyConnectedSpaceOfCompactSpace` gives finitely many components.

The class is stable under many constructions: `IsOpen.locallyConnectedSpace` for open subspaces, `Topology.IsOpenEmbedding.locallyConnectedSpace` for open embeddings, `Topology.IsCoinducing.locallyConnectedSpace` for quotients, `Prod.locallyConnectedSpace` for products, and `Pi.locallyConnectedSpace_of_finite` for finite products. For an infinite product, `Pi.locallyConnectedSpace_iff` says that the product is locally connected if and only if it is empty, or each factor is locally connected and only finitely many factors are not preconnected. The instance `Pi.locallyConnectedSpace` covers the case where each factor is preconnected. A discrete space is locally connected by `DiscreteTopology.toLocallyConnectedSpace`. A locally path connected space is locally connected, see Section 2.

#### Totally disconnected spaces

The module `Mathlib.Topology.Connected.TotallyDisconnected` defines the predicate `IsTotallyDisconnected s`: each preconnected subset of $s$ has at most one point. The class `TotallyDisconnectedSpace X` of Section 1 says this for `Set.univ`. The forms with components are `totallyDisconnectedSpace_iff_connectedComponent_singleton` and `totallyDisconnectedSpace_iff_connectedComponent_subsingleton`. The class is stable under `Subtype.totallyDisconnectedSpace`, `Prod.totallyDisconnectedSpace`, `Pi.totallyDisconnectedSpace` and `instTotallyDisconnectedSpaceSigma`, and it transfers along embeddings by `Topology.IsEmbedding.isTotallyDisconnected`.

The predicate `IsTotallySeparated s` says that each two distinct points of $s$ lie in two disjoint open sets that cover $s$. The class is `TotallySeparatedSpace X`. The usual form is `totallySeparatedSpace_iff_exists_isClopen`: each two distinct points are separated by a clopen set. The relations are:

- `TotallySeparatedSpace.totallyDisconnectedSpace` and `isTotallyDisconnected_of_isTotallySeparated`;
- `TotallySeparatedSpace.t2Space`, in the module `Mathlib.Topology.Connected.Separation`;
- `instTotallySeparatedSpaceOfT0SpaceOfZeroDimensionalSpace`: a zero dimensional $T_0$ space is totally separated;
- `instZeroDimensionalSpaceOfT2SpaceOfTotallyDisconnectedSpaceOfWeaklyLocallyCompactSpace`: a locally compact Hausdorff totally disconnected space is zero dimensional, so it is totally separated;
- `instTotallySeparatedSpaceOfIsUltrametricDist`: an ultrametric space is totally separated.

Maps into a totally disconnected space are constant on components. The statement is `Continuous.image_connectedComponent_eq_singleton`. For a connected source, `TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace` identifies `C(X, Y)` with $Y$.

#### The space of components

The quotient `ConnectedComponents X` uses the setoid `connectedComponentSetoid X`. The coercion from $X$ is continuous (`ConnectedComponents.continuous_coe`) and a quotient map (`ConnectedComponents.isQuotientMap_coe`). Two points have the same image if and only if they have the same component (`ConnectedComponents.coe_eq_coe`). The instance `ConnectedComponents.totallyDisconnectedSpace` makes the quotient totally disconnected. A compact space has a compact space of components by `instCompactSpaceConnectedComponents`, and `ConnectedComponents.discreteTopology_iff` says that the quotient is discrete if and only if each component is open.

The universal property has two parts. A continuous map $f : X \to Y$ into a totally disconnected space factors through the quotient as `Continuous.connectedComponentsLift`, with `Continuous.connectedComponentsLift_comp_coe` and `Continuous.connectedComponentsLift_unique`. Each continuous map $X \to Y$ induces `Continuous.connectedComponentsMap` between the spaces of components.

**Theorem.** Let $X$ be locally connected. Then the space of components of $X$ is discrete.

*Proof sketch.* By `ConnectedComponents.discreteTopology_iff`, it is sufficient to show that each component is open. Let $y$ be a point of the component $C$ of $x$. Since $X$ is locally connected, $y$ has a connected open neighborhood $V$. Then $V \cup C$ is connected, so $V \subseteq C$. Thus $C$ is a neighborhood of each of its points.

The module `Mathlib.Topology.Connected.CardComponents` counts components with open and closed maps. Let $f : X \to Y$ be open, closed and continuous, with $Y$ connected. Then each fiber meets each component of $X$, so `IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton` bounds the number of components of $X$ by the size of any fiber. The form `IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton` gives finitely many components of $X$ when $Y$ has finitely many components and the fibers are finite. Covering maps with finite fibers, which Volume 27 describes, are an application.

#### Common errors

1. Confusing totally disconnected with totally separated. The class `TotallyDisconnectedSpace` does not give clopen sets, and it does not give a Hausdorff space. Use `TotallySeparatedSpace` and `totallySeparatedSpace_iff_exists_isClopen` when a clopen set is necessary, or the zero dimensional instance for a locally compact Hausdorff space.
2. Expecting open components without local connectedness. In $\mathbb{Q}$ the components are points, and they are not open. The lemma `isOpen_connectedComponent` needs `LocallyConnectedSpace X`.
3. Using `TopologicalSpace.Clopens.exists_finset_eq_sup_prod` without compactness. The decomposition into finitely many boxes needs `CompactSpace` on both factors. For only one compact factor, use `TopologicalSpace.Clopens.exists_prod_subset`.

### Exercises

1. (A) Prove that the union of two clopen sets is clopen, and that the preimage of a clopen set under a continuous map is clopen. Find the lemmas.
2. (A) Show that each discrete space is totally separated, and find the instance `TotallySeparatedSpace.of_discrete`.
3. (B) Prove that a compact locally connected space has finitely many components. Use `isOpen_connectedComponent` and a finite subcover.
4. (B) Let $f : X \to Y$ be continuous with $Y$ totally disconnected and $X$ connected. Prove that $f$ is constant, with `Continuous.image_connectedComponent_eq_singleton`.
5. (B) Prove that `ConnectedComponents X` is totally disconnected for each space $X$.
6. (C) Let $X$ and $Y$ be compact. Prove `TopologicalSpace.Clopens.exists_finset_eq_sup_prod` from `TopologicalSpace.Clopens.exists_prod_subset` and compactness of $W$.

### Reference

<?reference?>
