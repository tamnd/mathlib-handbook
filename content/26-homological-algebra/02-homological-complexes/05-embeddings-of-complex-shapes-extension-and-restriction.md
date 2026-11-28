---
title: "Embeddings of complex shapes: extension and restriction"
kind: api
modules:
  - Mathlib.Algebra.Homology.Embedding.Boundary
  - Mathlib.Algebra.Homology.Embedding.Extend
  - Mathlib.Algebra.Homology.Embedding.ExtendHomology
  - Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
  - Mathlib.Algebra.Homology.Embedding.Restriction
  - Mathlib.Algebra.Homology.Embedding.RestrictionHomology
  - Mathlib.Algebra.Homology.Embedding.HomEquiv
  - Mathlib.Algebra.Homology.Embedding.IsSupported
  - Mathlib.Algebra.Homology.Embedding.AreComplementary
  - Mathlib.Algebra.Homology.Embedding.Connect
explains:
  E2: [HomologicalComplex.extend, HomologicalComplex.extendHomologyIso, HomologicalComplex.quasiIso_extendMap_iff, ComplexShape.Embedding.fullyFaithfulExtendFunctor, HomologicalComplex.restriction, ComplexShape.Embedding.homEquiv, HomologicalComplex.IsSupported, ComplexShape.Embedding.BoundaryGE, ComplexShape.Embedding.AreComplementary, CochainComplex.ConnectData.cochainComplex]
  E1: auto
families: []
requires: [V25.C02, V26.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Embeddings of complex shapes: extension and restriction

### Overview

Complexes come with many index sets: chain complexes on $\mathbb{N}$, cochain complexes on $\mathbb{Z}$, complexes that live between two bounds. Chapter 6, Section 1 defines an embedding $e : c \to c'$ of complex shapes, an injective map of indices that sends relations to relations. The main example is $n \mapsto p + n$ from $\mathbb{N}$ to $\mathbb{Z}$. This section describes the two basic operations along an embedding. Extension turns a complex of shape $c$ into a complex of shape $c'$ by adding zero objects. Restriction turns a complex of shape $c'$ into a complex of shape $c$ by forgetting the objects outside the image.

The modules prove that extension is fully faithful and preserves homology, homotopies and quasi-isomorphisms. They compute the homology of a restriction, describe the maps into an extension, and define the support of a complex. Two more modules treat a pair of complementary embeddings, such as $\mathbb{Z}_{\le n}$ and $\mathbb{Z}_{\ge n+1}$, and the gluing of a chain complex and a cochain complex into one complex on $\mathbb{Z}$. The truncations of the next section use all these tools.

Throughout, $e$ is an embedding of type `ComplexShape.Embedding` from $c$ to $c'$ with the index map `ComplexShape.Embedding.f`, and $C$ has a zero object.

### The library around it

#### Extension

Let $K$ be a complex of shape $c$. The extension `HomologicalComplex.extend K e` has the object $K_i$ in degree $e(i)$ and a zero object in every degree that is not in the image of $e$. Its differential from $e(i)$ to $e(j)$ is $d_{ij}$, and it is zero elsewhere. Since $e$ is injective, the definition is by cases on whether a degree has a preimage. The library hides the cases behind two lemmas.

1. `HomologicalComplex.extendXIso K e h` is the isomorphism $(K.\mathrm{extend}\ e)_{i'} \cong K_i$ when `h : e.f i = i'`.
2. `HomologicalComplex.isZero_extend_X` says that the object in degree $i'$ is zero when $i'$ is not in the image.

The lemma `HomologicalComplex.extend_d_eq` gives the differential through these isomorphisms. The functor form is `ComplexShape.Embedding.extendFunctor e C`, and the map of complexes is `HomologicalComplex.extendMap`. The functor is additive, and `ComplexShape.Embedding.fullyFaithfulExtendFunctor` says that it is fully faithful: a map of extensions has zero components outside the image, so it is determined by its components on the image. The extension of a single complex is a single complex (`HomologicalComplex.extendSingleIso`). The instances `HomologicalComplex.instProjectiveXExtend` and `HomologicalComplex.instInjectiveXExtend` say that the objects of an extension of a complex of projective (or injective) objects are projective (or injective), because a zero object is both.

#### The homology of an extension

**Proposition.** Let $j' = e(j)$. Then $H_{j'}(K.\mathrm{extend}\ e) \cong H_j(K)$. In a degree $j'$ outside the image of $e$, the extension is exact.

*Proof sketch.* Outside the image the object is zero, so the homology is zero. At $j' = e(j)$, the short complex of the extension at $j'$ is $X \to K_j \to Y$, where $X$ is $K_{i}$ if the previous index of $j'$ is $e(i)$, and zero otherwise, and the same holds for $Y$. In each case the kernel and the cokernel agree with those of the short complex of $K$ at $j$. The module builds explicit left and right homology data for this comparison. $\square$

In Lean the isomorphism is `HomologicalComplex.extendHomologyIso`, with `HomologicalComplex.extendCyclesIso` and `HomologicalComplex.extendOpcyclesIso` for cycles and opcycles. The lemma `HomologicalComplex.extend_exactAt` covers the degrees outside the image, and `HomologicalComplex.extend_exactAt_iff` the degrees inside. So a map $\varphi$ is a quasi-isomorphism if and only if its extension is one (`HomologicalComplex.quasiIso_extendMap_iff`), and `HomologicalComplex.instQuasiIsoExtendMap` is the instance.

Homotopies extend in the same way, when $e$ satisfies `ComplexShape.Embedding.IsRelIff`, that is, when $c.\mathrm{Rel}\, i\, j$ holds exactly when $c'.\mathrm{Rel}\, e(i)\, e(j)$. Then `Homotopy.extendEquiv` is a bijection between homotopies $f \simeq g$ and homotopies between the extended maps. The inverse is `Homotopy.ofExtend`. So extension induces a functor of homotopy categories, `ComplexShape.Embedding.extendHomotopyFunctor`, which is full and faithful (the instances `ComplexShape.Embedding.instFullHomotopyCategoryExtendHomotopyFunctor` and `ComplexShape.Embedding.instFaithfulHomotopyCategoryExtendHomotopyFunctor`). The lemma `HomologicalComplex.homotopyEquivalences_extendMap_iff` says that a map is a homotopy equivalence if and only if its extension is one.

#### Restriction

Let $e$ satisfy `ComplexShape.Embedding.IsRelIff` and let $K$ have shape $c'$. The restriction `HomologicalComplex.restriction K e` has $K_{e(i)}$ in degree $i$ and the differentials of $K$. The lemmas `HomologicalComplex.restriction_X` and `HomologicalComplex.restriction_d` give its data, and `ComplexShape.Embedding.restrictionFunctor` is the functor form. Restriction is additive.

The homology of a restriction needs a condition, because restriction forgets objects that the homology at the boundary can see. The isomorphism `HomologicalComplex.restrictionHomologyIso` takes three indices $i, j, k$ of $c$ with $e(i)$, $e(j)$, $e(k)$ the previous, current and next index of $e(j)$ in $c'$. Then $H_j(K.\mathrm{restriction}\ e) \cong H_{e(j)}(K)$. The same holds for cycles (`HomologicalComplex.restrictionCyclesIso`) and opcycles (`HomologicalComplex.restrictionOpcyclesIso`). The short complex isomorphism `HomologicalComplex.restriction.sc'Iso` is the core of the proof: under the condition, the two short complexes are the same.

#### Maps into an extension

Let $K$ have shape $c'$ and $L$ shape $c$. A map $K \to L.\mathrm{extend}\ e$ is zero outside the image of $e$, so it is determined by a map $K.\mathrm{restriction}\ e \to L$. Not every such map extends. At an index $j$ of $c$ whose previous index $i'$ in $c'$ is not in the image, the map must kill the image of $d : K_{i'} \to K_{e(j)}$. The predicate `ComplexShape.Embedding.HasLift` states this condition, and `ComplexShape.Embedding.homEquiv` is the bijection
$$\operatorname{Hom}(K, L.\mathrm{extend}\ e) \simeq \{ \varphi : K.\mathrm{restriction}\ e \to L \mid \varphi \text{ has a lift} \}.$$
The two directions are `ComplexShape.Embedding.homRestrict` and `ComplexShape.Embedding.liftExtend`. The lemmas `ComplexShape.Embedding.mono_liftExtend_f_iff`, `ComplexShape.Embedding.epi_liftExtend_f_iff` and `ComplexShape.Embedding.isIso_liftExtend_f_iff` test the components of the lift.

The boundary that appears here has a name. An index $j$ of $c$ is in the lower boundary, `ComplexShape.Embedding.BoundaryGE e j`, if some $i'$ with $c'.\mathrm{Rel}\, i'\, e(j)$ is outside the image of $e$. For the embedding $n \mapsto p + n$ of $\mathbb{N}$ in $\mathbb{Z}$, the lower boundary is $\{0\}$ (`ComplexShape.boundaryGE_embeddingUpIntGE_iff`). The dual notion is `ComplexShape.Embedding.BoundaryLE`. Outside the boundary, the previous index commutes with $e$ (`ComplexShape.Embedding.prev_f_of_not_boundaryGE`). An embedding of type `ComplexShape.Embedding.IsTruncLE` has an empty lower boundary (`ComplexShape.Embedding.BoundaryGE.false_of_isTruncLE`).

#### Support

A complex $K$ of shape $c'$ is strictly supported on $e$, `HomologicalComplex.IsStrictlySupported K e`, if $K_{i'}$ is zero for each $i'$ outside the image of $e$. It is supported on $e$, `HomologicalComplex.IsSupported K e`, if $K$ is only exact at these degrees. Strict support implies support (`HomologicalComplex.instIsSupportedOfIsStrictlySupported`), and an extension is strictly supported (`HomologicalComplex.instIsStrictlySupportedExtend`). The lemma `HomologicalComplex.exactAt_of_isSupported` uses the class, and `HomologicalComplex.isSupported_iff_of_quasiIso` says that support is invariant under quasi-isomorphism. Strict support is not: a quasi-isomorphism can change the objects.

The predicates `HomologicalComplex.IsStrictlySupportedOutside` and `HomologicalComplex.IsSupportedOutside` state the conditions in the degrees inside the image. They are structures and not classes, since in practice they are the support conditions for a complementary embedding. A complex is zero if and only if it is strictly supported inside and outside $e$ (`HomologicalComplex.isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside`).

#### Complementary embeddings

Two embeddings $e_1 : c_1 \to c$ and $e_2 : c_2 \to c$ are complementary, `ComplexShape.Embedding.AreComplementary e₁ e₂`, if their images form a partition of the indices of $c$. The main example is `ComplexShape.Embedding.embeddingUpInt_areComplementary`: for $n_0 + 1 = n_1$, the embeddings of $\mathbb{Z}_{\le n_0}$ and $\mathbb{Z}_{\ge n_1}$ in $\mathbb{Z}$ are complementary. The structure gives the disjointness (`ComplexShape.Embedding.AreComplementary.disjoint`) and the union (`ComplexShape.Embedding.AreComplementary.union`), and `ComplexShape.Embedding.AreComplementary.desc` defines a map out of the indices of $c$ by cases. The lemma `ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside₁_iff` says that "strictly supported outside $e_1$" is "strictly supported on $e_2$".

When $e_1$ is a truncation from above and $e_2$ a truncation from below, there is a short sequence $\tau_{\le} K \to K \to \tau_{\ge} K$. The map `HomologicalComplex.shortComplexTruncLEX₃ToTruncGE` goes from the cokernel of $\tau_{\le} K \to K$ to $\tau_{\ge} K$, and the instance `HomologicalComplex.instQuasiIsoShortComplexTruncLEX₃ToTruncGE` says that it is a quasi-isomorphism. The next section uses this map for the canonical truncations of a cochain complex.

#### Connecting a chain complex and a cochain complex

Let $K$ be a chain complex on $\mathbb{N}$, $L$ a cochain complex on $\mathbb{N}$, and $d_0 : K_0 \to L^0$ with $d_0 \circ d_1^K = 0$ and $d^0_L \circ d_0 = 0$. The structure `CochainComplex.ConnectData K L` holds these data, and `CochainComplex.ConnectData.cochainComplex` is the complex on $\mathbb{Z}$
$$\cdots \to K_1 \to K_0 \xrightarrow{d_0} L^0 \to L^1 \to \cdots,$$
with $K_0$ in degree $-1$ and $L^0$ in degree $0$. Away from the junction, its homology is the homology of $L$ or of $K$. For $n \ne 0$, `CochainComplex.ConnectData.homologyIsoPos` gives the isomorphism with $H^n(L)$ in degree $n$, and `CochainComplex.ConnectData.homologyIsoNeg` the isomorphism with $H_n(K)$ in degree $-(n+1)$. The restrictions to the two halves are `CochainComplex.ConnectData.restrictionGEIso` and `CochainComplex.ConnectData.restrictionLEIso`. For example, a projective resolution and an injective resolution of the same object connect in this way, with $d_0$ the composite $K_0 \to X \to L^0$.

#### Common errors

1. `HomologicalComplex.extendXIso` takes a proof of $e(i) = i'$, not an index $i'$ that Lean computes. A rewrite of the degree before applying it gives a motive error; pass the equation instead.
2. Restriction needs the instance `ComplexShape.Embedding.IsRelIff`, but extension does not. The homotopy results of extension also need it.
3. The degrees near the junction of `CochainComplex.ConnectData.cochainComplex` have no simple homology formula. The isomorphisms `CochainComplex.ConnectData.homologyIsoPos` and `CochainComplex.ConnectData.homologyIsoNeg` need `NeZero n`.

### Exercises

1. (A) Let $e : \mathbb{N} \to \mathbb{Z}$ be $n \mapsto n$ for the shapes `ComplexShape.up`. Describe `HomologicalComplex.extend K e` for a cochain complex $K$ on $\mathbb{N}$, and compute its homology in degree $-3$.
2. (A) Prove that the extension of a zero map is zero, and find the lemma.
3. (B) Show that the restriction of a strictly supported complex along $e$ followed by the extension along $e$ is isomorphic to the complex.
4. (B) For the embedding of $\mathbb{Z}_{\ge 0}$ in $\mathbb{Z}$, give a map $K.\mathrm{restriction}\ e \to L$ that does not satisfy `ComplexShape.Embedding.HasLift`.
5. (B) Over the ring $\mathbb{Z}/4$, connect the projective resolution $\cdots \xrightarrow{2} \mathbb{Z}/4 \xrightarrow{2} \mathbb{Z}/4$ of $\mathbb{Z}/2$ with the injective resolution $\mathbb{Z}/4 \xrightarrow{2} \mathbb{Z}/4 \xrightarrow{2} \cdots$ through $d_0 = 2$. Show that the result is exact in every degree.
6. (C) Prove that `HomologicalComplex.IsSupported` is invariant under quasi-isomorphism, from the definition of exactness.

### Reference

<?reference?>
