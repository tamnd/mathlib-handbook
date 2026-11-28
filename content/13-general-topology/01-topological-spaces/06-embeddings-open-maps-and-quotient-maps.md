---
title: Embeddings, open maps, quotient maps and local homeomorphisms
kind: api
modules:
  - Mathlib.Topology.Maps.Basic
  - Mathlib.Topology.Maps.OpenQuotient
  - Mathlib.Topology.Hom.Open
  - Mathlib.Topology.Maps.Strict.Basic
  - Mathlib.Topology.Maps.Strict.Group
  - Mathlib.Topology.Maps.Strict.Module
  - Mathlib.Topology.IsLocalHomeomorph
  - Mathlib.Topology.LocalAtTarget
explains:
  E2: [Topology.isInducing_iff_nhds, Topology.IsInducing.continuous_iff, Topology.IsQuotientMap.continuous_iff, IsOpenMap.isQuotientMap, Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap, isOpenMap_iff_nhds_le, IsOpenQuotientMap.iff_isOpenMap_isQuotientMap, Topology.IsStrictMap, Topology.isEmbedding_iff_isStrictMap_injective, IsLocalHomeomorph, IsLocalHomeomorph.isOpenMap, TopologicalSpace.IsOpenCover.isOpenMap_iff_restrictPreimage]
  E1: auto
families: []
requires: [V01, V04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Embeddings, open maps, quotient maps and local homeomorphisms

### Overview

Section 3 defined the induced and the coinduced topologies, and the predicates that say that a map carries one of them. A map $f : X \to Y$ is *inducing* when $X$ has the topology induced by $f$, and *coinducing* when $Y$ has the topology coinduced by $f$. An embedding is an injective inducing map, and a quotient map is a surjective coinducing map. An open map sends open sets to open sets, and a closed map sends closed sets to closed sets. These predicates appear in almost every construction of a space, because they say which maps into or out of the space are continuous.

This section describes the large library of lemmas about these predicates in `Mathlib.Topology.Maps.Basic`, and four smaller modules around it: open quotient maps, bundled continuous open maps, the strict maps of Bourbaki, and local homeomorphisms. A last module shows that most of these properties are local on the target: they can be checked on the pieces of an open cover of $Y$.

### The library around it

#### The predicates and their names

All the predicates of this section live in the namespace Topology, except `IsOpenMap`, `IsClosedMap`, `IsOpenQuotientMap` and `IsLocalHomeomorph`. Each predicate is a structure, so a proof gives the fields and a hypothesis gives access to them.

| Lean name | Meaning |
|---|---|
| `Topology.IsInducing f` | the topology of $X$ is induced by $f$ |
| `Topology.IsCoinducing f` | the topology of $Y$ is coinduced by $f$ |
| `Topology.IsEmbedding f` | inducing and injective |
| `Topology.IsOpenEmbedding f` | an embedding with open range |
| `Topology.IsClosedEmbedding f` | an embedding with closed range |
| `Topology.IsQuotientMap f` | coinducing and surjective |
| `IsOpenMap f` | the image of each open set is open |
| `IsClosedMap f` | the image of each closed set is closed |
| `IsOpenQuotientMap f` | surjective, continuous and open |

An inducing map is continuous (`Topology.IsInducing.continuous`), and so is a coinducing map (`Topology.IsCoinducing.continuous`). An open map or a closed map need not be continuous. Each structure has lemmas for the identity, for the composition and for a factor of a composition, for example `Topology.IsEmbedding.id`, `Topology.IsEmbedding.comp` and `Topology.IsEmbedding.of_comp`. The lemma `Topology.IsEmbedding.of_comp_iff` removes a known factor. The projections between the predicates are named by the target: `Topology.IsOpenEmbedding.isEmbedding`, `Topology.IsEmbedding.isInducing`, `Topology.IsClosedEmbedding.isClosedMap`, `Topology.IsOpenEmbedding.isOpenMap`.

#### Inducing maps and embeddings

The main tool is the universal property `Topology.IsInducing.continuous_iff`: if $g$ is inducing, then $f$ is continuous if and only if $g \circ f$ is continuous. So a map into a subspace is continuous when its composite with the inclusion is continuous. The neighbourhood form is `Topology.isInducing_iff_nhds`:

$$f \text{ is inducing} \iff \mathcal{N}(x) = f^{*}\,\mathcal{N}(f(x)) \text{ for each } x,$$

where $f^{*}$ is the preimage of a filter, `Filter.comap`. Chapter 2 defines this preimage. The open and closed sets of $X$ are the preimages of the open and closed sets of $Y$ (`Topology.IsInducing.isOpen_iff`, `Topology.IsInducing.isClosed_iff`), and the closure of $s$ is the preimage of the closure of $f(s)$ (`Topology.IsInducing.closure_eq_preimage_closure_image`). Limits transfer: `Topology.IsInducing.tendsto_nhds_iff` and `Topology.IsEmbedding.tendsto_nhds_iff`.

Embeddings arise from inverses. `Function.LeftInverse.isEmbedding` says: if $f \circ g = \mathrm{id}$ with $f$ and $g$ continuous, then $g$ is an embedding. The reason: for $U$ open in the domain of $g$, the equality $U = g^{-1}(f^{-1}(U))$ shows that $U$ is the preimage of an open set under $g$, and $g$ is injective because it has a left inverse. A subspace of a discrete space is discrete, `Topology.IsEmbedding.discreteTopology`.

#### Open embeddings and closed embeddings

The criteria are `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap` and `Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap`: a continuous injective open map is an open embedding, and a continuous injective closed map is a closed embedding. The proof of the first: let $U \subseteq X$ be open. Then $f(U)$ is open, and $U = f^{-1}(f(U))$ because $f$ is injective. So each open set of $X$ is a preimage of an open set, and $f$ is inducing. Its range $f(X)$ is open because $f$ is an open map. The converse forms are `Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap` and `Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap`. For an open embedding, a set is open if and only if its image is open, `Topology.IsOpenEmbedding.isOpen_iff_image_isOpen`, and continuity at a point transfers, `Topology.IsOpenEmbedding.continuousAt_iff`.

#### Open maps and closed maps

The filter form of openness is `isOpenMap_iff_nhds_le`: $f$ is open if and only if $\mathcal{N}(f(x)) \le f_{*}\mathcal{N}(x)$ for each $x$. In words: the image of each neighbourhood of $x$ is a neighbourhood of $f(x)$. A continuous open map satisfies $f_{*}\mathcal{N}(x) = \mathcal{N}(f(x))$, which is `IsOpenMap.map_nhds_eq`. The closure form of closedness is `isClosedMap_iff_closure_image`: $\overline{f(s)} \subseteq f(\overline{s})$ for each $s$. With continuity this becomes an equality, `IsClosedMap.closure_image_eq_of_continuous`. Open continuous maps commute with the preimage of closure, interior and frontier: `IsOpenMap.preimage_closure_eq_closure_preimage`, `IsOpenMap.preimage_interior_eq_interior_preimage` and `IsOpenMap.preimage_frontier_eq_frontier_preimage`. A useful criterion is `IsOpenMap.of_sections`: a map that has a local continuous section through each point is open.

#### Quotient maps

The universal property of a quotient map is `Topology.IsQuotientMap.continuous_iff`: if $f$ is a quotient map, then $g$ is continuous if and only if $g \circ f$ is continuous. The closed set form of the definition is `Topology.isQuotientMap_iff_isClosed`. The two standard sources of quotient maps are `IsOpenMap.isQuotientMap` and `IsClosedMap.isQuotientMap`: a continuous surjective map that is open, or closed, is a quotient map. The proof for the open case: let $V \subseteq Y$ with $f^{-1}(V)$ open. Since $f$ is surjective, $V = f(f^{-1}(V))$, and this set is open because $f$ is open. Continuity gives the converse direction.

The module `Mathlib.Topology.Maps.OpenQuotient` treats the structure `IsOpenQuotientMap`. The equivalence `IsOpenQuotientMap.iff_isOpenMap_isQuotientMap` says that an open quotient map is the same as a quotient map that is open. Open quotient maps behave better than general quotient maps: the image of the neighbourhood filter is the neighbourhood filter, `IsOpenQuotientMap.map_nhds_eq`, so continuity at a point can be tested upstairs, `IsOpenQuotientMap.continuousAt_comp_iff`. The quotient map of a topological group by a subgroup is the main example.

#### Bundled continuous open maps

The module `Mathlib.Topology.Hom.Open` defines the type `ContinuousOpenMap α β`, written `α →CO β`, of continuous open maps, and the class `ContinuousOpenMapClass` for types of such maps. It follows the pattern of the bundled maps of the library: a coercion to functions, the extensionality lemma `ContinuousOpenMap.ext`, the identity `ContinuousOpenMap.id`, the composition `ContinuousOpenMap.comp`, and the simp lemmas `ContinuousOpenMap.coe_comp` and `ContinuousOpenMap.comp_apply`. The forgetful map to `C(α, β)` is `ContinuousOpenMap.toContinuousMap`.

#### Strict maps

A continuous map $f : X \to Y$ factors as $X \to f(X) \to Y$. The map $f$ is *strict*, `Topology.IsStrictMap f`, when the first factor $X \to f(X)$ is a quotient map onto the range with its subspace topology. This is the definition, and `Topology.isStrictMap_iff_isQuotientMap_rangeFactorization` states it. An equivalent form, `Topology.isStrictMap_iff_isHomeomorph_quotientKerEquivRange`, says that the bijection $X / {\sim_f} \to f(X)$ from the quotient by the relation "same image" is a homeomorphism. The data form of this homeomorphism is `Homeomorph.quotientKerEquivRange`.

The strict maps contain the two classes above: `Topology.isEmbedding_iff_isStrictMap_injective` says that the embeddings are the injective strict maps, and `Topology.isQuotientMap_iff_isStrictMap_surjective` says that the quotient maps are the surjective strict maps. Continuous open maps and continuous closed maps are strict, by `IsOpenMap.isStrictMap` and `IsClosedMap.isStrictMap`. For a continuous homomorphism of topological groups, `MonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict` reduces strictness to the openness of $G \to f(G)$, and `ContinuousMulEquiv.quotientKerEquivRange` gives the isomorphism theorem $G / \ker f \cong f(G)$ as an isomorphism of topological groups. The module `Mathlib.Topology.Maps.Strict.Module` gives the same results for linear maps: `LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict` and `ContinuousLinearEquiv.quotKerEquivRange`.

#### Local homeomorphisms

A map $f : X \to Y$ is a local homeomorphism, `IsLocalHomeomorph f`, when each point $x$ lies in an open set $U$ such that $f$ restricts to a homeomorphism from $U$ onto an open set of $Y$. Mathlib states this with an open partial homeomorphism `OpenPartialHomeomorph X Y` whose source contains $x$ and whose underlying function is $f$. The relative form is `IsLocalHomeomorphOn f s`. The form without partial homeomorphisms is `isLocalHomeomorph_iff_isOpenEmbedding_restrict`: each point has a neighbourhood on which $f$ is an open embedding. The covering map $\mathbb{R} \to S^1$, $t \mapsto e^{2\pi i t}$, is a local homeomorphism, and each open embedding is one, `Topology.IsOpenEmbedding.isLocalHomeomorph`.

A local homeomorphism is continuous and open (`IsLocalHomeomorph.continuous`, `IsLocalHomeomorph.isOpenMap`), and it is locally injective (`IsLocalHomeomorph.isLocallyInjective`). It keeps neighbourhood filters, `IsLocalHomeomorph.map_nhds_eq`. An injective local homeomorphism is an open embedding, `IsLocalHomeomorph.isOpenEmbedding_of_injective`, and a bijective one is a homeomorphism, `IsLocalHomeomorph.toHomeomorphOfBijective`. Local homeomorphisms compose, `IsLocalHomeomorph.comp`. The local inverse at a point is `IsLocalHomeomorph.localInverseAt`.

#### Properties local on the target

Let $(U_i)$ be an open cover of $Y$, given as `TopologicalSpace.IsOpenCover U`. For $f : X \to Y$, the map `(U i).carrier.restrictPreimage f` is the restriction $f^{-1}(U_i) \to U_i$. The module `Mathlib.Topology.LocalAtTarget` proves that many properties hold for $f$ if and only if they hold for each restriction.

| Lean name | Property that is local on the target |
|---|---|
| `TopologicalSpace.IsOpenCover.isOpenMap_iff_restrictPreimage` | open map |
| `TopologicalSpace.IsOpenCover.isClosedMap_iff_restrictPreimage` | closed map |
| `TopologicalSpace.IsOpenCover.isInducing_iff_restrictPreimage` | inducing (for continuous $f$) |
| `TopologicalSpace.IsOpenCover.isEmbedding_iff_restrictPreimage` | embedding (for continuous $f$) |
| `TopologicalSpace.IsOpenCover.isOpenEmbedding_iff_restrictPreimage` | open embedding |
| `TopologicalSpace.IsOpenCover.isClosedEmbedding_iff_restrictPreimage` | closed embedding |
| `TopologicalSpace.IsOpenCover.isHomeomorph_iff_restrictPreimage` | homeomorphism (for continuous $f$) |

The base case is `TopologicalSpace.IsOpenCover.isOpen_iff_coe_preimage`: a set is open if and only if its trace on each $U_i$ is open in $U_i$. One direction of each row holds for any subset $s \subseteq Y$: `IsOpenMap.restrictPreimage`, `Set.restrictPreimage_isEmbedding` and their companions say that the restriction $f^{-1}(s) \to s$ keeps the property. Algebraic geometry uses these results to check properties of morphisms of schemes on an affine cover.

#### Common errors

1. A bijective continuous map need not be a homeomorphism, and a continuous injective map need not be an embedding. The map $[0, 2\pi) \to S^1$, $t \mapsto e^{it}$, is a continuous bijection, and its inverse is not continuous at $1$. Openness, closedness or a compactness argument is needed.
2. The names of the predicates start with Is and live in the namespace Topology: write `Topology.IsEmbedding`, or open the namespace. Older texts use names without the prefix Is, and these names no longer work.
3. A quotient map need not be open. The quotient $\mathbb{R} \to \mathbb{R}/\mathbb{Z}$ by a group is open, but the map that collapses $[0, 1]$ to a point is a closed quotient map that is not open. The lemmas `IsOpenQuotientMap.map_nhds_eq` and `IsOpenQuotientMap.continuousAt_comp_iff` need the open form.

### Exercises

1. (A) Prove that the composition of two quotient maps is a quotient map, and find the lemma of the library.
2. (A) Show that the inclusion of $[0, 1]$ in $\mathbb{R}$ is a closed embedding and not an open map.
3. (B) Prove `Topology.IsQuotientMap.continuous_iff` from the definition of the coinduced topology.
4. (B) Let $f : X \to Y$ be a continuous closed surjection. Prove that $\overline{f(s)} = f(\overline{s})$ for each $s \subseteq X$.
5. (B) Prove that an injective local homeomorphism is an open embedding.
6. (C) Give a continuous surjective map that is neither open nor closed but is a quotient map, and a strict map that is neither injective nor surjective.

### Reference

<?reference?>
