---
title: Sober, spectral and Priestley spaces
kind: api
modules:
  - Mathlib.Topology.Specialization
  - Mathlib.Topology.Sober
  - Mathlib.Topology.NoetherianSpace
  - Mathlib.Topology.QuasiSeparated
  - Mathlib.Topology.Spectral.Basic
  - Mathlib.Topology.Spectral.Prespectral
  - Mathlib.Topology.Spectral.Hom
  - Mathlib.Topology.Spectral.ConstructibleTopology
  - Mathlib.Topology.Sets.CompactOpenCovered
  - Mathlib.Topology.Order.Hom.Basic
  - Mathlib.Topology.Order.Hom.Esakia
  - Mathlib.Topology.Order.Priestley
  - Mathlib.Topology.Order.HullKernel
  - Mathlib.Topology.Order.Category.FrameAdjunction
explains:
  E2: [QuasiSober, IsGenericPoint, irreducibleSetEquivPoints, TopologicalSpace.NoetherianSpace, QuasiSeparatedSpace, SpectralSpace, IsSpectralMap, constructibleTopology, PriestleySpace, EsakiaHom]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C04, V13.C05, V13.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sober, spectral and Priestley spaces

### Overview

The spaces of algebraic geometry and of the duality theory of lattices are far from Hausdorff. The prime spectrum of a ring has a point for each prime ideal, and the closure of a point is the set of the primes that contain it. These spaces are described by the specialization order and by their compact open sets. A space is sober if each irreducible closed set is the closure of a unique point. A space is spectral if it is sober, compact and T0, and its compact open sets form a basis that is closed under finite intersections. The theorem of Hochster says that the spectral spaces are exactly the prime spectra of rings.

This section describes the order structure of a space, sober spaces and their generic points, Noetherian and quasi-separated spaces, spectral spaces and spectral maps, the constructible topology, and the ordered spaces of Priestley duality and Esakia duality. It ends with the hull-kernel topology and the adjunction between spaces and locales.

The text uses the specialization order of Chapter 4, compactness from Chapter 5, the irreducible sets of Chapter 6 and the lower topology of Section 6.

### The library around it

#### The specialization order

The type synonym `Specialization α` carries the specialization order of a space $\alpha$: $a \le b$ when $b$ specializes to $a$, that is when $b \in \overline{\{a\}}$ (`Specialization.toEquiv_le_toEquiv`). A continuous map gives a monotone map `Specialization.map`, and the functor `topToPreord` from topological spaces to preorders packs this. For an Alexandrov-discrete space the open sets are the upper sets of this order (`Specialization.isUpperSet_ofEquiv_preimage`), and the space is homeomorphic to its specialization order with the upper set topology of Section 6 (`homeoWithUpperSetTopologyorderIso`).

#### Sober spaces and generic points

A point $x$ is a generic point of a set $S$ if $S$ is the closure of $x$. This is `IsGenericPoint x S`. A generic point lies in each open set that meets $S$ (`IsGenericPoint.mem_open_set_iff`), and it specializes to each point of $S$ (`IsGenericPoint.specializes`). A set with a generic point is closed and irreducible (`IsGenericPoint.isClosed`, `IsGenericPoint.isIrreducible`). In a T0 space a set has at most one generic point (`IsGenericPoint.eq`).

The class `QuasiSober α` says that each irreducible closed set has a generic point. The choice is `IsIrreducible.genericPoint`, and `genericPoint α` is the generic point of an irreducible space. A sober space is a quasi-sober T0 space. In a sober space the points correspond to the irreducible closed sets:

$$\alpha \cong_o \{\text{irreducible closed subsets of } \alpha\}, \qquad x \mapsto \overline{\{x\}}.$$

This is `irreducibleSetEquivPoints`, an order isomorphism. The set `genericPoints α` of the generic points of the irreducible components is dense in a quasi-sober space (`genericPoints.closure`). Quasi-sobriety is local: a space with an open cover by quasi-sober subspaces is quasi-sober (`TopologicalSpace.IsOpenCover.quasiSober`). It passes to open and to closed subspaces (`Topology.IsOpenEmbedding.quasiSober`, `Topology.IsClosedEmbedding.quasiSober`). A Hausdorff space is quasi-sober, and so is each R1 space (`R1Space.quasiSober`), since its irreducible sets are the sets of pairwise inseparable points.

#### Noetherian and quasi-separated spaces

A space is Noetherian if the closed sets satisfy the descending chain condition. This is `TopologicalSpace.NoetherianSpace`. The main criterion is compactness of all subsets:

$$\alpha \text{ Noetherian} \iff \text{each subset of } \alpha \text{ is compact.}$$

This is `TopologicalSpace.noetherianSpace_iff_isCompact`, and `TopologicalSpace.noetherianSpace_tfae` adds more forms, such as compactness of each open set. *Proof sketch of one direction.* Let each open set be compact, and let $U_0 \subseteq U_1 \subseteq \dots$ be open sets. The union $U$ is open, so compact, and it is covered by finitely many $U_i$. So the chain is stationary, and the complements give the descending chain condition for closed sets. A Noetherian space has finitely many irreducible components (`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`), and each closed set is a finite union of irreducible closed sets (`TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`). A Hausdorff Noetherian space is finite (`TopologicalSpace.NoetherianSpace.finite`). Subspaces, images and finite unions of Noetherian spaces are Noetherian.

A space is quasi-separated if the intersection of two compact open sets is compact. This is `QuasiSeparatedSpace`, and `IsQuasiSeparated s` is the relative form for a set. A Hausdorff space is quasi-separated (`T2Space.to_quasiSeparatedSpace`), since there compact sets are closed. A Noetherian space is quasi-separated (`NoetherianSpace.to_quasiSeparatedSpace`), since there each set is compact. The property passes to open subspaces (`Topology.IsOpenEmbedding.quasiSeparatedSpace`).

#### Spectral spaces and spectral maps

A space is prespectral if its compact open sets form a basis. This is `PrespectralSpace`. In a prespectral space the open sets correspond to the ideals of the lattice of compact open sets (`PrespectralSpace.opensEquiv`), and each compact set inside an open set has a compact open set between them (`PrespectralSpace.exists_isCompact_and_isOpen_between`). The class `SpectralSpace` puts together the T0, compact, quasi-sober, quasi-separated and prespectral conditions. An open compact subspace of a spectral space is spectral (`Topology.IsOpenEmbedding.spectralSpace`).

A map is spectral if it is continuous and the preimage of each compact open set is compact. This is `IsSpectralMap`, and the bundled maps are `SpectralMap α β`. Spectral maps compose (`IsSpectralMap.comp`), and a proper map is spectral (`IsProperMap.isSpectralMap`). The morphisms of schemes that are quasi-compact are spectral maps on the underlying spaces.

The module `Mathlib.Topology.Sets.CompactOpenCovered` defines when a set is a finite union of images of compact open sets under a family of maps (`IsCompactOpenCovered`). If the maps are open and continuous on prespectral spaces, each compact open set in the union of the ranges has this property (`IsCompactOpenCovered.of_isOpenMap`). The notion is used for the covers of the fpqc topology of schemes.

#### The constructible topology

The constructible topology `constructibleTopology X` is generated by the compact open sets of $X$ and their complements (`constructibleTopologySubbasis`). The type synonym `WithConstructibleTopology X` carries it. The compact open sets become clopen (`IsCompact.isClopen_constructibleTopology_of_isOpen`). For a compact quasi-separated space it is generated by the constructible sets of Chapter 1 (`constructibleTopology_eq_generateFrom_isConstructible`). For a spectral space the new topology is compact (`compactSpace_withConstructibleTopology`). It is also Hausdorff and totally disconnected, so a spectral space with the constructible topology is a Stone space.

#### Priestley and Esakia spaces

An ordered space is a Priestley space if two points with $x \not\le y$ are separated by a clopen upper set:

$$x \not\le y \implies \exists U \text{ clopen upper set},\ x \in U,\ y \notin U.$$

This is `PriestleySpace`, with the consequences `exists_isClopen_upper_of_not_le` and `exists_isClopen_lower_of_not_le`. A Priestley space is totally separated (`PriestleySpace.toTotallySeparatedSpace`). In Priestley duality the compact Priestley spaces correspond to the bounded distributive lattices: the lattice of a space is the lattice of its clopen upper sets, the type `ClopenUpperSet` of Chapter 1.

The morphisms of ordered spaces are `ContinuousOrderHom α β`, written `α →Co β`: monotone continuous maps. An Esakia morphism is a continuous order map with the back condition: if $f(a) \le b$, then $b = f(c)$ for some $c \ge a$. This is `EsakiaHom α β`. The order part alone is `PseudoEpimorphism α β`. These maps are the morphisms of Esakia duality between Esakia spaces and Heyting algebras.

#### The hull-kernel topology and points of a frame

Let $T$ be a set of elements of a complete lattice $\alpha$. The hull of $a$ is $\{p \in T : a \le p\}$ (`PrimitiveSpectrum.hull`), and the kernel of $S \subseteq T$ is its infimum (`PrimitiveSpectrum.kernel`). They form a Galois connection (`PrimitiveSpectrum.gc`). If each element of $T$ is inf-prime, the lower topology of Section 6 restricted to $T$ has as open sets the complements of the hulls (`PrimitiveSpectrum.isOpen_iff`). This is the hull-kernel topology. The prime spectrum of a ring and the primitive spectrum of a C*-algebra are examples.

The module `Mathlib.Topology.Order.Category.FrameAdjunction` gives each complete lattice $L$ a space of points `Locale.PT L`: the frame homomorphisms from $L$ to the lattice of propositions. The open sets are the sets of points that send a fixed $u \in L$ to true (`Locale.PT.isOpen_iff`). The functor `Locale.pt` from locales to topological spaces is a right adjoint of the functor that takes the frame of open sets (`Locale.adjunctionTopToLocalePT`). The spaces for which the unit is a homeomorphism are the sober spaces.

#### Common errors

1. `QuasiSober` does not include T0. A sober space in the usual sense is `[QuasiSober α] [T0Space α]`, and the uniqueness of generic points (`IsGenericPoint.eq`) needs T0.
2. The specialization order of `Specialization α` puts the generic point at the bottom: $a \le b$ when $b$ is in the closure of $a$. In the prime spectrum this is the inclusion of prime ideals. The upper set topology of Section 6 uses the reverse convention for its specialization relation.
3. A spectral map is not only a continuous map. The condition on preimages of compact open sets is extra. The map from an infinite discrete space to a point is continuous and not spectral, since the preimage of the point is not compact.

### Exercises

1. (A) Show that a T2 space is sober, and that a set with the cofinite topology is sober if and only if it is finite.
2. (A) Prove that a Noetherian space has only finitely many irreducible components, from `TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`.
3. (B) Prove that the intersection of two compact open sets in a Hausdorff space is compact, and give a compact space with two compact open sets whose intersection is not compact.
4. (B) Let $f : X \to Y$ be a continuous map. Prove that $f$ is monotone for the specialization orders.
5. (B) Show that each finite T0 space is spectral.
6. (C) Prove that in a spectral space the constructible topology is Hausdorff, and that it has the compact open sets of the original topology as clopen sets.

### Reference

<?reference?>
