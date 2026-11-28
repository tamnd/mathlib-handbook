---
title: Cycles, differentials and homology of spectral objects
kind: api
modules:
  - Mathlib.Algebra.Homology.SpectralObject.Cycles
  - Mathlib.Algebra.Homology.SpectralObject.Differentials
  - Mathlib.Algebra.Homology.SpectralObject.Homology
  - Mathlib.Algebra.Homology.SpectralObject.EpiMono
  - Mathlib.Algebra.Homology.SpectralObject.FirstPage
  - Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
explains:
  E2: [CategoryTheory.Abelian.SpectralObject.cycles, CategoryTheory.Abelian.SpectralObject.opcycles, CategoryTheory.Abelian.SpectralObject.toCycles, CategoryTheory.Abelian.SpectralObject.Ψ, CategoryTheory.Abelian.SpectralObject.d, CategoryTheory.Abelian.SpectralObject.dHomologyIso, CategoryTheory.Abelian.SpectralObject.mono_map, CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso, CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.HasFirstPageComputation, HomotopyCategory.spectralObjectMappingCone]
  E1: auto
families: []
requires: [V25.C05, V26.C02, V26.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cycles, differentials and homology of spectral objects

### Overview

Section 2 defines a spectral object $X$ in an abelian category $C$, indexed by a category $\iota$, with objects $H^n(f)$ for each morphism $f$ of $\iota$ and connecting morphisms $\delta : H^n(g) \to H^{n+1}(f)$ for composable $f$ and $g$. The object $E^n(f_1, f_2, f_3)$ is the homology of $H^{n-1}(f_3) \to H^n(f_2) \to H^{n+1}(f_1)$. This section gives the tools that make the objects $E^n$ into the pages of a spectral sequence. The kernel of one $\delta$ and the cokernel of the other are the cycles and the opcycles. Five composable morphisms give a differential between two objects $E$, and its square is zero. Seven composable morphisms give a short complex of objects $E$, and its homology is again an object $E$. This is the step from one page to the next.

The section also gives the maps between objects $E$ that are monomorphisms, epimorphisms or isomorphisms, and the computation of the first page in terms of the objects $H^n$. These are the facts that make a spectral sequence of a bounded spectral object stop at a finite page. The last module gives the main source of spectral objects: the mapping cones of cochain complexes, as a spectral object with values in the homotopy category of Chapter 3.

Throughout, $X$ is a spectral object in the sense of `CategoryTheory.Abelian.SpectralObject`, the integers $n_0, n_1, n_2, \dots$ satisfy $n_{k} + 1 = n_{k+1}$, and these equalities are arguments that an arithmetic tactic fills by default.

### The library around it

#### Cycles and opcycles

For composable $f : i \to j$ and $g : j \to k$, the object `CategoryTheory.Abelian.SpectralObject.cycles` $X$ $f$ $g$ $n$ is the kernel $Z^n(f, g)$ of $\delta : H^n(g) \to H^{n+1}(f)$. The object `CategoryTheory.Abelian.SpectralObject.opcycles` $X$ $f$ $g$ $n$ is the cokernel of $\delta : H^{n-1}(g) \to H^n(f)$. The exact sequence of a spectral object gives two other forms of these objects. For $f \circ g$ written $fg$, the cycles are the cokernel of $H^n(f) \to H^n(fg)$, and the opcycles are the kernel of $H^n(fg) \to H^n(g)$. The main data are:

| Lean name | Statement |
|---|---|
| `CategoryTheory.Abelian.SpectralObject.iCycles` | the monomorphism $Z^n(f, g) \to H^n(g)$ |
| `CategoryTheory.Abelian.SpectralObject.pOpcycles` | the epimorphism $H^n(f) \to$ the opcycles |
| `CategoryTheory.Abelian.SpectralObject.toCycles` | the epimorphism $H^n(fg) \to Z^n(f, g)$ |
| `CategoryTheory.Abelian.SpectralObject.fromOpcycles` | the monomorphism from the opcycles to $H^n(fg)$ |
| `CategoryTheory.Abelian.SpectralObject.cokernelIsoCycles` | the cokernel of $H^n(f) \to H^n(fg)$ is isomorphic to $Z^n(f, g)$ |
| `CategoryTheory.Abelian.SpectralObject.opcyclesIsoKernel` | the opcycles are isomorphic to the kernel of $H^n(fg) \to H^n(g)$ |
| `CategoryTheory.Abelian.SpectralObject.kernelSequenceCycles_exact` | the sequence $0 \to Z^n(f, g) \to H^n(g) \to H^{n+1}(f)$ is exact |
| `CategoryTheory.Abelian.SpectralObject.cokernelSequenceOpcycles_exact` | the dual sequence for the opcycles is exact |

To make a morphism to the cycles, use `CategoryTheory.Abelian.SpectralObject.liftCycles` with a morphism to $H^n(g)$ whose composition with $\delta$ is zero. The dual is `CategoryTheory.Abelian.SpectralObject.descOpcycles`. For three composable morphisms, `CategoryTheory.Abelian.SpectralObject.δToCycles` is the morphism $H^{n}(f_3) \to Z^{n+1}(f_1, f_2)$ that $\delta$ induces, and `CategoryTheory.Abelian.SpectralObject.δFromOpcycles` is the dual. The maps `CategoryTheory.Abelian.SpectralObject.cyclesMap` and `CategoryTheory.Abelian.SpectralObject.opcyclesMap` give the functoriality along morphisms of `CategoryTheory.ComposableArrows` $\iota$ $2$. The lemma `CategoryTheory.Abelian.SpectralObject.isZero_cycles` says that $Z^n(f, g) = 0$ when $H^n(g) = 0$, and `CategoryTheory.Abelian.SpectralObject.isIso_toCycles` says that `CategoryTheory.Abelian.SpectralObject.toCycles` is an isomorphism when $H^n(f) = 0$.

The object $E^n(f_1, f_2, f_3)$ of Section 2 is a quotient of $Z^n(f_1, f_2)$ and a subobject of the opcycles of $f_2$ and $f_3$ in degree $n$. The epimorphism is `CategoryTheory.Abelian.SpectralObject.πE` and the monomorphism is `CategoryTheory.Abelian.SpectralObject.ιE`, in the module `Mathlib.Algebra.Homology.SpectralObject.Page`.

#### The differentials

For three composable morphisms, `CategoryTheory.Abelian.SpectralObject.Ψ` is the morphism from $Z^n(f_2, f_3)$ to the opcycles of $f_1$ and $f_2$ in degree $n+1$. Two connecting morphisms induce it: $\delta : H^n(f_2 f_3) \to H^{n+1}(f_1)$, by the lemma `CategoryTheory.Abelian.SpectralObject.toCycles_Ψ`, and $\delta : H^n(f_3) \to H^{n+1}(f_1 f_2)$, by `CategoryTheory.Abelian.SpectralObject.Ψ_fromOpcycles`. The four term sequence `CategoryTheory.Abelian.SpectralObject.sequenceΨ` is
$$Z^n(f_1 f_2, f_3) \to Z^n(f_2, f_3) \xrightarrow{\Psi} \mathrm{opZ}^{n+1}(f_1, f_2) \to \mathrm{opZ}^{n+1}(f_1, f_2 f_3),$$
and `CategoryTheory.Abelian.SpectralObject.sequenceΨ_exact` says that it is exact.

For five composable morphisms $f_1, \dots, f_5$, the differential `CategoryTheory.Abelian.SpectralObject.d` is a morphism
$$d : E^n(f_3, f_4, f_5) \to E^{n+1}(f_1, f_2, f_3).$$
The lemma `CategoryTheory.Abelian.SpectralObject.πE_d_ιE` says that $\iota_E \circ d \circ \pi_E = \Psi$ for the morphisms $f_2, f_3, f_4$. The lemma `CategoryTheory.Abelian.SpectralObject.d_d` says that two consecutive differentials compose to zero, for seven composable morphisms. The isomorphism `CategoryTheory.Abelian.SpectralObject.EIsoH` identifies $E^n(1, f, 1)$ with $H^n(f)$. When $f_1$, $f_3$ and $f_5$ are identities, the lemma `CategoryTheory.Abelian.SpectralObject.d_EIsoH_hom` says that $d$ is $\delta$ under these isomorphisms.

#### The homology of the differentials

For seven composable morphisms $f_1, \dots, f_7$, `CategoryTheory.Abelian.SpectralObject.dShortComplex` is the short complex
$$E^{n-1}(f_5, f_6, f_7) \to E^n(f_3, f_4, f_5) \to E^{n+1}(f_1, f_2, f_3).$$
The homology data `CategoryTheory.Abelian.SpectralObject.dHomologyData` has these parts:

| Part | Object |
|---|---|
| cycles | $E^n(f_2 f_3, f_4, f_5)$ |
| opcycles | $E^n(f_3, f_4, f_5 f_6)$ |
| homology | $E^n(f_2 f_3, f_4, f_5 f_6)$ |

So `CategoryTheory.Abelian.SpectralObject.dHomologyIso` identifies the homology of the short complex with $E^n(f_2 f_3, f_4, f_5 f_6)$. This is the formula $E_{r+1} = H(E_r)$: on a page, the three morphisms are steps of length $r$ in a filtration, and on the next page the outer steps are longer by one. The exact sequences under it are `CategoryTheory.Abelian.SpectralObject.dKernelSequence_exact`, for $0 \to E^n(f_2 f_3, f_4, f_5) \to E^n(f_3, f_4, f_5) \to E^{n+1}(f_1, f_2, f_3)$, and its dual `CategoryTheory.Abelian.SpectralObject.dCokernelSequence_exact`.

#### Monomorphisms, epimorphisms and isomorphisms

A morphism of `CategoryTheory.ComposableArrows` $\iota$ $3$ induces a morphism `CategoryTheory.Abelian.SpectralObject.map` between the objects $E^n$. The module `Mathlib.Algebra.Homology.SpectralObject.EpiMono` studies two cases:

| Lean name | Statement |
|---|---|
| `CategoryTheory.Abelian.SpectralObject.epi_map` | a morphism that changes only the last arrow, from $(f_1, f_2, f_3)$ to $(f_1, f_2, f_3')$, gives an epimorphism |
| `CategoryTheory.Abelian.SpectralObject.mono_map` | a morphism that changes only the first arrow, from $(f_1, f_2, f_3)$ to $(f_1', f_2, f_3)$, gives a monomorphism |
| `CategoryTheory.Abelian.SpectralObject.isIso_map_fourδ₄Toδ₃_of_isZero` | the map $E^n(f_1, f_2, f_3) \to E^n(f_1, f_2, f_3 f_4)$ is an isomorphism if $H^n(f_4) = 0$ |
| `CategoryTheory.Abelian.SpectralObject.isIso_map_fourδ₁Toδ₀_of_isZero` | the map $E^n(f_2 f_3, f_4, f_5) \to E^n(f_3, f_4, f_5)$ is an isomorphism if $H^{n+1}(f_2) = 0$ |
| `CategoryTheory.Abelian.SpectralObject.map_fourδ₁Toδ₀_d` | the composition of that map with the differential is zero |

For a spectral object indexed by a preorder, the abbreviations `CategoryTheory.Abelian.SpectralObject.mapFourδ₁Toδ₀'` and `CategoryTheory.Abelian.SpectralObject.mapFourδ₄Toδ₃'` are the same maps written with inequalities $i_0 \le i_1 \le \dots$, and `CategoryTheory.Abelian.SpectralObject.isoMapFourδ₁Toδ₀'` is the isomorphism. These statements say when a page no longer changes: if the objects $H$ of the short steps at the ends are zero, the differentials into and out of a page are zero, and the next page is the same object.

#### The first page

For a term of `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore`, the class `CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.HasFirstPageComputation` says that on the first page $r_0$ the indices $i_0$ and $i_1$ are equal, and the indices $i_2$ and $i_3$ are equal. Then the outer morphisms are identities, and `CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso` identifies the object of the page $r_0$ in position $pq$ with $H^n(i_1 \le i_2)$, for the degree $n$ of $pq$. The lemma `CategoryTheory.Abelian.SpectralObject.spectralSequence_first_page_d_eq` says that the differential of the first page is $\delta$ under these isomorphisms. Instances give the class for `CategoryTheory.Abelian.SpectralObject.coreE₂Cohomological`, `CategoryTheory.Abelian.SpectralObject.coreE₂CohomologicalNat` and `CategoryTheory.Abelian.SpectralObject.coreE₂HomologicalNat` of Section 2, so the $E_2$ page of those spectral sequences is computed by the objects $H$.

#### The spectral object of mapping cones

Let $C$ be an additive category. The functor `HomotopyCategory.composableArrowsFunctor` sends a morphism $f$ of cochain complexes to its mapping cone `CochainComplex.mappingCone`. The spectral object `HomotopyCategory.spectralObjectMappingCone` is indexed by the category of cochain complexes indexed by $\mathbb{Z}$, and it takes values in the homotopy category. It sends $f$ to the image of its mapping cone, and its connecting morphisms come from the triangle `CochainComplex.mappingConeCompTriangle` of a composition. It is a spectral object in the triangulated sense, `CategoryTheory.Triangulated.SpectralObject`. A homological functor to an abelian category, such as a cohomology functor, turns it into an abelian spectral object through `CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor`. Composition with a functor from $\iota$ to cochain complexes, for example a filtered complex, gives a spectral object indexed by $\iota$.

#### Common errors

1. The cycles $Z^n(f, g)$ are a subobject of $H^n(g)$, the second argument, and the opcycles are a quotient of $H^n(f)$, the first argument. A proof that uses `CategoryTheory.Abelian.SpectralObject.iCycles` with the wrong morphism does not typecheck, and the error message names objects of the form `(X.H n).obj (ComposableArrows.mk₁ f)`.
2. `CategoryTheory.Abelian.SpectralObject.d` goes from $E^n(f_3, f_4, f_5)$ to $E^{n+1}(f_1, f_2, f_3)$. The source uses the last three arrows and the target uses the first three, so the shared arrow $f_3$ is the last arrow of the target and the first arrow of the source.
3. `HomotopyCategory.spectralObjectMappingCone` is not an abelian spectral object. It has no objects $E^n$ until a homological functor is applied.

### Exercises

1. (A) From the exact sequence $H^n(f) \to H^n(fg) \to H^n(g) \to H^{n+1}(f)$, prove that $Z^n(f, g)$ is isomorphic to the cokernel of $H^n(f) \to H^n(fg)$, as in `CategoryTheory.Abelian.SpectralObject.cokernelIsoCycles`.
2. (A) Show that $Z^n(f, g) = 0$ if $H^n(g) = 0$, and that `CategoryTheory.Abelian.SpectralObject.toCycles` is an isomorphism if $H^n(f) = 0$.
3. (B) For a spectral object indexed by the preorder $0 \le 1 \le 2 \le 3$, write the objects of $E^n(0 \le 1 \le 2 \le 3)$ and $E^n(0 \le 0 \le 1 \le 1)$, and say which of them is an object $H^n$.
4. (B) Use `CategoryTheory.Abelian.SpectralObject.dHomologyIso` to compute the homology of the short complex for seven arrows when $f_2$ and $f_6$ are identities.
5. (B) For a spectral object indexed by $\mathbb{Z}$ with $H^n(i \le j) = 0$ when $j \le 0$ or $i \ge 5$, show with `CategoryTheory.Abelian.SpectralObject.isIso_map_fourδ₁Toδ₀_of_isZero` that the pages become constant after a finite number of steps.
6. (C) For a short exact sequence of cochain complexes $0 \to K \to L \to M \to 0$ seen as two composable morphisms $0 \to K \to L$, explain how `HomotopyCategory.spectralObjectMappingCone` and a cohomology functor give the long exact sequence of cohomology.

### Reference

<?reference?>
