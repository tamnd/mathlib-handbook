---
title: The library of homeomorphisms
kind: api
modules:
  - Mathlib.Topology.Homeomorph.Lemmas
  - Mathlib.Topology.Homeomorph.Quotient
  - Mathlib.Topology.Homeomorph.TransferInstance
explains:
  E2: [isHomeomorph_iff_continuous_bijective, isHomeomorph_iff_isEmbedding_surjective, isHomeomorph_iff_isQuotientMap_injective, Topology.IsEmbedding.toHomeomorph, Homeomorph.piCongr, Homeomorph.Set.prod, Homeomorph.piSplitAt, Homeomorph.Quotient.congr, Equiv.homeomorph, Homeomorph.isCompact_image]
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

## The library of homeomorphisms

### Overview

Section 3 defined a homeomorphism `X ≃ₜ Y` as an equivalence of types whose two directions are continuous, and the predicate `IsHomeomorph f` for a function that is a homeomorphism. Two kinds of facts come after the definition. First, criteria: conditions under which a continuous bijection is a homeomorphism. Second, a catalogue of standard homeomorphisms: the canonical bijections between products, function spaces, subtypes and quotients are continuous in both directions, and the library gives each one as a named homeomorphism.

This section describes the module `Mathlib.Topology.Homeomorph.Lemmas`, which holds both kinds of facts, and two small modules: `Mathlib.Topology.Homeomorph.Quotient` for quotients and `Mathlib.Topology.Homeomorph.TransferInstance` for the transport of a topology along an equivalence. The section is a reference for the reader who needs a homeomorphism and wants to know its name.

### The library around it

#### Data and property

A homeomorphism is data: `e : X ≃ₜ Y` contains the function, its inverse and the two proofs of continuity. The property `IsHomeomorph f` says that a given function $f$ has this form. The bridge between them is `isHomeomorph_iff_exists_homeomorph`: $f$ is a homeomorphism if and only if $f$ is the function of some `e : X ≃ₜ Y`. For an equivalence `e : X ≃ Y`, the lemma `Equiv.isHomeomorph_iff` says that $e$ is a homeomorphism if and only if $e$ and $e^{-1}$ are continuous. A homeomorphism is an embedding, an open embedding, a closed embedding, a quotient map and a dense embedding, by `IsHomeomorph.isEmbedding`, `IsHomeomorph.isOpenEmbedding`, `IsHomeomorph.isClosedEmbedding`, `IsHomeomorph.isQuotientMap` and `Homeomorph.isDenseEmbedding`.

#### Criteria

The property `IsHomeomorph f` has several characterisations. Each one names the missing piece that turns a continuous bijection into a homeomorphism.

| Lean name | $f$ is a homeomorphism if and only if |
|---|---|
| `isHomeomorph_iff_isEmbedding_surjective` | $f$ is an embedding and surjective |
| `isHomeomorph_iff_isQuotientMap_injective` | $f$ is a quotient map and injective |
| `isHomeomorph_iff_continuous_isClosedMap_bijective` | $f$ is continuous, closed and bijective |
| `isHomeomorph_iff_exists_inverse` | $f$ is continuous and has a continuous two sided inverse |
| `isHomeomorph_iff_continuous_bijective` | $f$ is continuous and bijective, when $X$ is compact and $Y$ is Hausdorff |

The proof of the second row is a good model. A homeomorphism is a quotient map and is injective. Conversely, let $f$ be an injective quotient map. It is surjective, so it is bijective. For an open $U \subseteq X$, the set $f(U)$ has preimage $f^{-1}(f(U)) = U$ because $f$ is injective, and this preimage is open, so $f(U)$ is open because $f$ is a quotient map. So $f$ is an open map, and the inverse of $f$ is continuous.

The last row is the theorem of the compact space and the Hausdorff space. A closed subset of the compact space $X$ is compact, its image is compact, and a compact subset of the Hausdorff space $Y$ is closed. So $f$ is a closed map, and the third row applies. Chapter 5 proves the two facts on compact sets. The data form is `Continuous.homeoOfEquivCompactToT2`, and `Continuous.continuous_symm_of_equiv_compact_to_t2` gives only the continuity of the inverse.

An embedding gives a homeomorphism onto its range, `Topology.IsEmbedding.toHomeomorph`, of type `X ≃ₜ Set.range f`. When $f$ is surjective, `Topology.IsEmbedding.toHomeomorphOfSurjective` gives `X ≃ₜ Y`. A homeomorphism restricts to the image of a set, `Homeomorph.image`. A bijection between discrete spaces is a homeomorphism, `Homeomorph.ofDiscrete`.

#### The catalogue

The canonical homeomorphisms follow the naming of the equivalences of Volume 1. A name in the namespace `Homeomorph` usually has an equivalence with the same name in the namespace `Equiv`, and the lemma `Homeomorph.toEquiv_piCongr` or a similar one says that the two have the same function. The simp lemmas such as `Homeomorph.piSplitAt_apply` and `Homeomorph.piSplitAt_symm_apply` give the values.

| Lean name | Homeomorphism |
|---|---|
| `Homeomorph.Set.univ` | $\mathrm{univ} \cong X$ |
| `Homeomorph.setCongr` | $s \cong t$ from $s = t$ |
| `Homeomorph.Set.prod` | $s \times t \cong s \times t$, a subtype of $X \times Y$ and a product of subtypes |
| `Homeomorph.subtype` | $\{x \mid p(x)\} \cong \{y \mid q(y)\}$ from $e$ with $p(x) \iff q(e(x))$ |
| `Homeomorph.piCongrLeft` | reindexing $\prod_i Y_{e(i)} \cong \prod_j Y_j$ along $e : \iota \simeq \iota'$ |
| `Homeomorph.piCongrRight` | $\prod_i Y_i \cong \prod_i Y'_i$ from $Y_i \cong Y'_i$ |
| `Homeomorph.piCongr` | both changes at once |
| `Homeomorph.funUnique` | $(\iota \to X) \cong X$ for $\iota$ with one element |
| `Homeomorph.finTwoArrow` | $(\mathrm{Fin}\ 2 \to X) \cong X \times X$ |
| `Homeomorph.piFinTwo` | $\prod_{i : \mathrm{Fin}\ 2} X_i \cong X_0 \times X_1$ |
| `Fin.appendHomeomorph` | $X^m \times X^n \cong X^{m+n}$ |
| `Homeomorph.piSplitAt` | $\prod_j Y_j \cong Y_i \times \prod_{j \ne i} Y_j$ |
| `Homeomorph.sumArrowHomeomorphProdArrow` | $(\iota \oplus \iota' \to X) \cong (\iota \to X) \times (\iota' \to X)$ |
| `Homeomorph.sumPiEquivProdPi` | the dependent form of the last row |
| `Homeomorph.sigmaProdDistrib` | $(\Sigma_i X_i) \times Y \cong \Sigma_i (X_i \times Y)$ |
| `Homeomorph.prodUnique` | $X \times Y \cong X$ for $Y$ with one element |
| `Homeomorph.ulift` | `ULift X` $\cong X$ |
| `Homeomorph.Set.iUnion` | $\bigcup_i s_i \cong \Sigma_i s_i$ for sets with disjoint neighbourhoods |

Each of these maps is continuous with a continuous inverse because of the universal properties of Section 3. For example, `Homeomorph.piSplitAt` sends $x$ to $(x_i, (x_j)_{j \ne i})$. Each coordinate of this map is a coordinate projection, so it is continuous by `continuous_pi` and `continuous_apply`. The inverse sends $(a, y)$ to the function that is $a$ at $i$ and $y_j$ at $j \ne i$. Its coordinate at $j$ is a projection of $a$ or of $y$, so it is continuous too. The property form of the products is `IsHomeomorph.prodMap`, `IsHomeomorph.pi_map`, `IsHomeomorph.sumMap` and `IsHomeomorph.sigmaMap`.

#### Invariants

A homeomorphism keeps each topological property. The library states this for the main ones, in two forms: an equivalence for the image or the preimage of a set, and an instance transfer for the whole space.

- Sets: `Homeomorph.isCompact_image`, `Homeomorph.isCompact_preimage`, `Homeomorph.isConnected_image`, `Homeomorph.isPreconnected_image`, `Homeomorph.isSigmaCompact_image`.
- Spaces: `Homeomorph.compactSpace`, `Homeomorph.locallyCompactSpace_iff`, `Homeomorph.secondCountableTopology`, `Homeomorph.baireSpace`, `Homeomorph.locallyConnectedSpace`, `Homeomorph.totallyDisconnectedSpace`.
- Filters: `Homeomorph.map_cocompact` says that the image of the filter of complements of compact sets is the same filter, and `Homeomorph.map_punctured_nhds_eq` treats the punctured neighbourhoods.
- Relative continuity: `Homeomorph.comp_continuousOn_iff` and `Homeomorph.comp_continuousWithinAt_iff` say that composition with a homeomorphism does not change continuity on a set.

The proofs are short because the image of a compact set by a continuous map is compact, and both $e$ and $e^{-1}$ are continuous. The lemma `Topology.IsCoinducing.connectedComponentsHomeomorph` is of another kind: a coinducing map with connected fibres induces a homeomorphism of the spaces of connected components.

#### Quotients

The module `Mathlib.Topology.Homeomorph.Quotient` lifts homeomorphisms to quotients. `Homeomorph.Quotient.congr` takes `e : X ≃ₜ Y` and setoids $r_X$, $r_Y$ with $r_X(x_1, x_2) \iff r_Y(e(x_1), e(x_2))$, and gives `Quotient rX ≃ₜ Quotient rY`. The forms for the quotient by an arbitrary relation are `Homeomorph.Quot.congr`, `Homeomorph.Quot.congrLeft` and `Homeomorph.Quot.congrRight`, and `Homeomorph.Quotient.congrRight` changes only the relation. Two trivial quotients are identified with the space: `Homeomorph.quotientBot` for the quotient by equality, the bottom setoid, and `Homeomorph.quotientTrivial` for a setoid whose classes are single points.

#### Transfer along an equivalence

The module `Mathlib.Topology.Homeomorph.TransferInstance` has two declarations. For an equivalence `e : α ≃ β` and a topology on $\beta$, `Equiv.topologicalSpace e` is the topology on $\alpha$ induced by $e$, and `Equiv.homeomorph e` is $e$ as a homeomorphism for this topology. This is the standard way to put a topology on a type that is in bijection with a known space, for example a structure with one field. The topology is a definition and not an instance, so a proof must make it a local instance first.

#### Common errors

1. A continuous bijection is not a homeomorphism in general. The identity from $\mathbb{R}$ with the discrete topology to $\mathbb{R}$ with the usual topology is a continuous bijection, and its inverse is not continuous. The compact to Hausdorff criterion needs both hypotheses.
2. `Homeomorph.Set.prod` has a subtype of a product on the left and a product of subtypes on the right. The two types are different, and Lean does not identify them without this homeomorphism.
3. After a local instance `Equiv.topologicalSpace e`, the type $\alpha$ has a second topology if it had one before. The two topologies are not equal in general, and lemmas about the old one do not apply.

### Exercises

1. (A) Write the homeomorphism $(\mathrm{Fin}\ 2 \to \mathbb{R}) \cong \mathbb{R} \times \mathbb{R}$ with its library name, and state its simp lemma.
2. (A) Prove that a homeomorphism maps the interior of a set to the interior of its image.
3. (B) Prove `isHomeomorph_iff_isEmbedding_surjective` from the definitions.
4. (B) Show that $[0, 1]$ and $\{0\} \cup \{1/n \mid n \ge 1\}$ are not homeomorphic, with an invariant from the list above or from Chapter 6.
5. (B) Use `isHomeomorph_iff_continuous_bijective` to prove that $[0, 1] / \{0 \sim 1\}$ is homeomorphic to the circle.
6. (C) Prove that $\mathbb{R}$ and $\mathbb{R}^2$ are not homeomorphic. Use the connectedness of the complement of a point, and the invariant `Homeomorph.isConnected_image`.

### Reference

<?reference?>
