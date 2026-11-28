---
title: "Hyperspaces: compact sets, the Vietoris topology and the Hausdorff uniformity"
kind: api
modules:
  - Mathlib.Topology.Sets.Compacts
  - Mathlib.Topology.Sets.BaseChangeNhds
  - Mathlib.Topology.Sets.VietorisTopology
  - Mathlib.Topology.UniformSpace.Closeds
explains:
  E2: [TopologicalSpace.Compacts, TopologicalSpace.Compacts.coe_inf, TopologicalSpace.CompactOpens.instGeneralizedBooleanAlgebra, TopologicalSpace.vietoris, TopologicalSpace.vietoris.specializes_iff_of_t1Space, TopologicalSpace.Compacts.isCompact_subsets_of_isCompact, hausdorffEntourage, mem_hausdorffEntourage, IsCompact.nhds_hausdorff_eq_nhds_vietoris, TopologicalSpace.Compacts.instCompleteSpace]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Hyperspaces: compact sets, the Vietoris topology and the Hausdorff uniformity

### Overview

A hyperspace is a space whose points are subsets of another space. The space of nonempty compact subsets of a metric space, with the Hausdorff distance, is the classical example. It is the home of fractals, of the attractors of iterated function systems and of the Gromov-Hausdorff theory. The library builds hyperspaces in three steps. First it makes the compact sets of $X$ into a type with an order. Then it puts the Vietoris topology on the sets of a topological space. Last it puts the Hausdorff uniformity on the sets of a uniform space, and it proves that the two agree on compact sets.

The modules are `Mathlib.Topology.Sets.Compacts` and `Mathlib.Topology.Sets.BaseChangeNhds` for the types of compact sets, `Mathlib.Topology.Sets.VietorisTopology` for the topology and `Mathlib.Topology.UniformSpace.Closeds` for the uniformity. The section uses compactness from Chapter 5, the types of open and closed sets from Chapter 1, and uniform spaces from Section 1 of this chapter.

### The library around it

#### Types of compact sets

The module `Mathlib.Topology.Sets.Compacts` follows the pattern of `TopologicalSpace.Opens` in Chapter 1. It defines four bundled types, each a `SetLike` type with an extensionality lemma and a field that holds the property.

| Lean name | Elements |
|---|---|
| `TopologicalSpace.Compacts X` | compact sets |
| `TopologicalSpace.NonemptyCompacts X` | nonempty compact sets |
| `TopologicalSpace.PositiveCompacts X` | compact sets with nonempty interior |
| `TopologicalSpace.CompactOpens X` | compact open sets |

The fields are `TopologicalSpace.Compacts.isCompact`, `TopologicalSpace.NonemptyCompacts.nonempty` and `TopologicalSpace.PositiveCompacts.interior_nonempty`. The maps `TopologicalSpace.NonemptyCompacts.toCompacts`, `TopologicalSpace.PositiveCompacts.toNonemptyCompacts` and `TopologicalSpace.CompactOpens.toOpens` forget part of the data. Positive compacts are the normalisation sets of Haar measure in Volume 18.

A finite union of compact sets is compact, so each type has a supremum with carrier the union: `TopologicalSpace.Compacts.coe_sup`, `TopologicalSpace.NonemptyCompacts.coe_sup` and `TopologicalSpace.PositiveCompacts.coe_sup`. The empty set is compact, so `Compacts X` has a bottom, with `TopologicalSpace.Compacts.coe_bot`. A top element exists only when $X$ is compact, by `TopologicalSpace.Compacts.instBoundedOrderOfCompactSpace`.

The infimum needs more care. In a Hausdorff space a compact set is closed, so the intersection $K \cap L$ is a closed subset of the compact set $K$, and so it is compact. This gives `TopologicalSpace.Compacts.coe_inf` and the instance `TopologicalSpace.Compacts.instDistribLatticeOfT2Space`, both with the hypothesis `T2Space X`. Without it the intersection of two compact sets can fail to be compact: in the line with two origins, two compact intervals that each contain one origin meet in a punctured interval.

For compact open sets the same argument gives more. In a Hausdorff space a compact open set is clopen, by `TopologicalSpace.CompactOpens.toClopens`. The difference $K \setminus L$ of two compact open sets is then a closed subset of $K$ and an open set, so it is a compact open set. So `CompactOpens X` is a generalized Boolean algebra, `TopologicalSpace.CompactOpens.instGeneralizedBooleanAlgebra`, with `TopologicalSpace.CompactOpens.coe_sdiff`. When $X$ is compact too, the top is $X$ and `TopologicalSpace.CompactOpens.instBooleanAlgebra` gives a Boolean algebra.

A continuous map sends compact sets to compact sets. This gives `TopologicalSpace.Compacts.map`, with `TopologicalSpace.Compacts.coe_map`, `TopologicalSpace.Compacts.map_id` and `TopologicalSpace.Compacts.map_comp`. The map of compact open sets, `TopologicalSpace.CompactOpens.map`, also needs `IsOpenMap f`. A homeomorphism gives an equivalence `TopologicalSpace.Compacts.equiv`. Products of compact sets are compact, and the instances `TopologicalSpace.Compacts.instSProdProd` and its companions let `K ×ˢ L` stay in the bundled types. In a locally compact space, each nonempty open set contains a positive compact, `exists_positiveCompacts_subset`.

#### Neighbourhoods of a compact set

The end of `Mathlib.Topology.Sets.Compacts` and the module `Mathlib.Topology.Sets.BaseChangeNhds` hold small order-theoretic tools for sheaf theory on locally compact spaces. For a compact set $K$, `TopologicalSpace.Compacts.openNhds K` is the set of open sets that contain $K$, `TopologicalSpace.Compacts.compactNhds K` is the set of compact sets that are neighbourhoods of $K$, and `TopologicalSpace.Compacts.openRcNhds K` is the set of open neighbourhoods of $K$ with compact closure. For an open set $U$, `TopologicalSpace.Opens.compactsInside U` is the set of compact sets inside $U$. The closure of a member of `openRcNhds K` is in `compactNhds K`, by `TopologicalSpace.Compacts.closure_mem_compactNhds_of_mem_openRcNhds`.

An inclusion $K \subseteq L$ sends the open neighbourhoods of $L$ to those of $K$, by `TopologicalSpace.Compacts.baseChangeOpenNhds`, with `TopologicalSpace.Compacts.baseChangeOpenNhds_id` and `TopologicalSpace.Compacts.baseChangeOpenNhds_comp`. A proper map $f$ pulls compact sets back, `TopologicalSpace.Compacts.properPreimage`, with carrier $f^{-1}(K)$ by `TopologicalSpace.Compacts.coe_properPreimage`. The instances of the form `TopologicalSpace.Compacts.instInitialElemOpensOpenRcNhdsCompactNhdsFunctorOfT2Space` say that some of these maps are initial functors. These facts let a limit over open neighbourhoods be computed over a smaller family.

#### The Vietoris topology

The Vietoris topology on `Set X` is `TopologicalSpace.vietoris X`. It is generated by two kinds of sets, for $U$ open in $X$:

$$\{s \mid s \subseteq U\} \quad\text{and}\quad \{s \mid s \cap U \ne \emptyset\}.$$

So a set $s$ is near $t$ when $s$ lies inside each open set around $t$ and $s$ meets each open set that $t$ meets. The lemmas `IsOpen.powerset_vietoris` and `TopologicalSpace.vietoris.isOpen_inter_nonempty_of_isOpen` say that these generators are open. The basis `TopologicalSpace.vietoris.isTopologicalBasis` has, for each finite family $u$ of open sets, the set of $s$ with $s \subseteq \bigcup u$ that meet each member of $u$. A function $f : Y \to \mathrm{Set}\ X$ is continuous if and only if the preimages of $\{s \mid s \subseteq U\}$ are open for open $U$ and those of $\{s \mid s \subseteq F\}$ are closed for closed $F$, by `TopologicalSpace.vietoris.continuous_iff`.

The Vietoris topology on all sets is far from Hausdorff. A set $s$ and its closure have the same neighbourhoods in one direction: `TopologicalSpace.vietoris.specializes_closure` says $s \rightsquigarrow \overline{s}$. In a $T_1$ space, `TopologicalSpace.vietoris.specializes_iff_of_t1Space` gives $s \rightsquigarrow t$ if and only if $s \subseteq t \subseteq \overline{s}$. The proof of the forward direction is short. If $x \in s \setminus t$, the open set $X \setminus \{x\}$ contains $t$ but not $s$. If $y \in t \setminus \overline{s}$, the open set $X \setminus \overline{s}$ meets $t$ but not $s$.

On compact sets the behaviour is better. The topologies `TopologicalSpace.Compacts.topology` and `TopologicalSpace.NonemptyCompacts.topology` are the subspace topologies. The hyperspace keeps many properties of $X$, each in a lemma of the form `P (Compacts X) ↔ P X`.

| Lean name | Property kept |
|---|---|
| `TopologicalSpace.Compacts.t2Space_iff` | Hausdorff |
| `TopologicalSpace.Compacts.regularSpace_iff` | regular |
| `TopologicalSpace.Compacts.compactSpace_iff` | compact |
| `TopologicalSpace.Compacts.locallyCompactSpace_iff` | locally compact |
| `TopologicalSpace.Compacts.secondCountableTopology_iff` | second countable |
| `TopologicalSpace.Compacts.separableSpace_iff` | separable |
| `TopologicalSpace.NonemptyCompacts.connectedSpace_iff` | connected |

The key compactness result is `TopologicalSpace.Compacts.isCompact_subsets_of_isCompact`: for compact $K$, the set of compact $L \subseteq K$ is compact. The finite sets are dense, `TopologicalSpace.Compacts.dense_setOfPred_finite`. The singleton map $x \mapsto \{x\}$ is an embedding, `TopologicalSpace.Compacts.isEmbedding_singleton`, and a closed embedding in a Hausdorff space. The union map is continuous, `TopologicalSpace.Compacts.instContinuousSup`. A continuous map induces a continuous map of hyperspaces, `Continuous.compacts_map`.

#### The Hausdorff uniformity

For a relation $U$ on $X$, the relation `hausdorffEntourage U` on sets holds for $(s, t)$ when each point of $s$ is $U$-close to a point of $t$, and each point of $t$ is $U$-close to a point of $s$. This is `mem_hausdorffEntourage`. For a metric space and $U = \{(x, y) \mid d(x, y) < \varepsilon\}$, it is close to the statement that the Hausdorff distance of $s$ and $t$ is at most $\varepsilon$. The construction respects the operations on relations: `hausdorffEntourage_comp`, `hausdorffEntourage_id`, `inv_hausdorffEntourage` and `monotone_hausdorffEntourage`. So the images of the entourages of $X$ form a uniformity on `Set X`, `UniformSpace.hausdorff X`.

The library puts this uniformity on three types: `TopologicalSpace.Closeds.uniformSpace`, `TopologicalSpace.Compacts.uniformSpace` and `TopologicalSpace.NonemptyCompacts.uniformSpace`. The lemmas `TopologicalSpace.Closeds.uniformity_def` and `TopologicalSpace.Compacts.uniformity_def` say that it is the pullback of the uniformity of `UniformSpace.hausdorff X` along the coercion. On all sets the uniformity cannot see the difference of $s$ and $\overline{s}$, by `UniformSpace.hausdorff.nhds_closure`, so the closed sets are the right type.

On compact sets the two hyperspace structures agree: `IsCompact.nhds_hausdorff_eq_nhds_vietoris` says that at a compact set the Hausdorff neighbourhoods and the Vietoris neighbourhoods are the same. At a totally bounded set only one inclusion holds, `TotallyBounded.nhds_vietoris_le_nhds_hausdorff`. So the Hausdorff uniformity on `Compacts X` induces the Vietoris topology.

Completeness passes to the hyperspace: `TopologicalSpace.Compacts.instCompleteSpace` and `TopologicalSpace.NonemptyCompacts.instCompleteSpace`. The proof uses the fact that the totally bounded sets form a closed set in the hyperspace, `UniformSpace.hausdorff.isClosed_setOfPred_totallyBounded`. A Cauchy filter of compact sets converges to the closure of its limit points. That closure is complete and totally bounded, so it is compact by Chapter 5. In a complete Hausdorff space the inclusion of compact sets in closed sets is a closed embedding, `TopologicalSpace.Compacts.isClosedEmbedding_toCloseds`. The lemmas `TopologicalSpace.Closeds.uniformContinuous_sup`, `TopologicalSpace.Compacts.uniformContinuous_singleton` and `UniformContinuous.compacts_map` give uniform continuity of the basic operations.

#### Common errors

1. The intersection of two terms of `TopologicalSpace.Compacts X` needs `T2Space X`. Without it there is no infimum instance, and `TopologicalSpace.Compacts.coe_inf` does not apply.
2. `TopologicalSpace.vietoris X` is not an instance on `Set X`. The instances are on `Compacts X` and `NonemptyCompacts X`. The type `Closeds X` carries the Hausdorff uniformity and not the Vietoris topology, and these two can differ on noncompact closed sets.
3. `TopologicalSpace.Compacts.map` takes the continuity proof as an explicit argument. It takes the map and then a proof of its continuity, so a term with the map alone is a function that still waits for the proof.

### Exercises

1. (A) Prove that a finite union of compact sets is compact, and deduce `TopologicalSpace.Compacts.coe_sup`.
2. (A) In a Hausdorff space, show that a compact open set is clopen, and that the difference of two compact open sets is compact open.
3. (B) Give a non-Hausdorff space with two compact sets whose intersection is not compact.
4. (B) In a $T_1$ space, prove that $s \rightsquigarrow t$ in the Vietoris topology if and only if $s \subseteq t \subseteq \overline{s}$.
5. (B) Prove that the finite sets are dense in `Compacts X` with the Vietoris topology.
6. (C) Prove that the space of nonempty compact subsets of a complete metric space is complete for the Hausdorff uniformity.

### Reference

<?reference?>
