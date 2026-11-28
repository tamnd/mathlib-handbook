---
title: Cocones, path objects and degreewise split sequences
kind: api
modules:
  - Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
  - Mathlib.Algebra.Homology.HomotopyFiber
  - Mathlib.Algebra.Homology.Precylinder
  - Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
  - Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
  - Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
  - Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
  - Mathlib.Algebra.Homology.HomotopyCategory.ChainComplex
  - Mathlib.Algebra.Homology.HomotopyCategory.Plus
explains:
  E2: [CochainComplex.mappingCocone, CochainComplex.mappingCocone.rotateTriangleIso, HomologicalComplex.homotopyFiber, HomologicalComplex.pathObject, HomologicalComplex.pathObject.lift, CochainComplex.triangleOfDegreewiseSplit, HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit, CochainComplex.mappingCone.quasiIso_descShortComplex, CochainComplex.quasiIso_shift_iff, HomotopyCategory.Plus]
  E1: auto
families: []
requires: [V24.C08, V25.C02, V25.C05, V26.C01, V26.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cocones, path objects and degreewise split sequences

### Overview

Section 2 makes the homotopy category of cochain complexes triangulated with the triangles of mapping cones. This section collects the modules that extend that construction. The mapping cocone gives the rotated triangle $\mathrm{Cocone}(\varphi) \to K \to L \to \mathrm{Cocone}(\varphi)[1]$. The homotopy fiber and the path object are the duals of the homotopy cofiber and the cylinder of Section 1, and two small modules package the cylinder and the path object for homotopical algebra.

A short exact sequence of complexes that splits in each degree gives a distinguished triangle in the homotopy category, and every distinguished triangle is isomorphic to one of this form. A short exact sequence that does not split still gives a quasi-isomorphism from the mapping cone of its first map to its third object, which the derived category of Chapter 5 uses. The section ends with the compatibility of homology with the shift, the single functors as a family that commutes with shifts, and the triangulated subcategory of bounded below complexes up to homotopy.

Throughout, $K$, $L$ are cochain complexes on $\mathbb{Z}$ in a preadditive category $C$ with binary biproducts, and $\varphi : K \to L$ is a morphism.

### The library around it

#### The mapping cocone

The complex `CochainComplex.mappingCocone` of $\varphi$ is defined as the shift by $-1$ of the mapping cone, so in degree $n$ it is $K^n \oplus L^{n-1}$. Its structure maps are given as cochains and cocycles of the Hom complex of Section 3:

| Lean name | Statement |
|---|---|
| `CochainComplex.mappingCocone.inl` | the $0$-cochain from $K$ to the cocone |
| `CochainComplex.mappingCocone.inr` | the $1$-cocycle from $L$ to the cocone |
| `CochainComplex.mappingCocone.fst` | the morphism of complexes from the cocone to $K$ |
| `CochainComplex.mappingCocone.snd` | the $(-1)$-cochain from the cocone to $L$ |
| `CochainComplex.mappingCocone.lift` | a morphism into the cocone from a morphism $\alpha : M \to K$ and a $(-1)$-cochain $\beta$ with $\delta \beta + \alpha\varphi = 0$ |
| `CochainComplex.mappingCocone.desc` | a morphism out of the cocone from a $0$-cochain and a $1$-cocycle that satisfy one equation |
| `CochainComplex.mappingCocone.triangle` | the triangle $\mathrm{Cocone}(\varphi) \to K \to L \to \mathrm{Cocone}(\varphi)[1]$ |
| `CochainComplex.mappingCocone.rotateTriangleIso` | the rotation of this triangle is isomorphic to the mapping cone triangle |

The versions `CochainComplex.mappingCocone.liftCochain`, `CochainComplex.mappingCocone.liftCocycle`, `CochainComplex.mappingCocone.descCochain` and `CochainComplex.mappingCocone.descCocycle` build cochains and cocycles of other degrees. So the cocone has the same API as the mapping cone, and the isomorphism with a rotation shows that its triangle is distinguished in the homotopy category.

#### Homotopy fibers and path objects

The module `Mathlib.Algebra.Homology.HomotopyFiber` dualizes the homotopy cofiber for complexes of every shape. The class `HomologicalComplex.HasHomotopyFiber` asks for the biproducts that the construction needs, and an instance gives it when $C$ has binary biproducts. The complex is `HomologicalComplex.homotopyFiber`.

The path object `HomologicalComplex.pathObject` of $K$ is the dual of the cylinder. It has a map `HomologicalComplex.pathObject.ι` from $K$ and two maps `HomologicalComplex.pathObject.π₀` and `HomologicalComplex.pathObject.π₁` back to $K$. A homotopy between $\varphi_0, \varphi_1 : F \to K$ is the same as a morphism to the path object, by `HomologicalComplex.pathObject.lift`. If every index has a successor for the shape, then `HomologicalComplex.pathObject.homotopyEquiv` says that $\iota$ is a homotopy equivalence and `HomologicalComplex.pathObject.homotopy₀₁` gives a homotopy between the two projections.

The module `Mathlib.Algebra.Homology.Precylinder` turns the cylinder into `HomologicalComplex.precylinder` and the path object into `HomologicalComplex.prepathObject`, the structures of homotopical algebra that Chapter 5, Section 4 uses for model categories.

#### Degreewise split short exact sequences

Let $S$ be a short complex $X_1 \to X_2 \to X_3$ of cochain complexes, with a splitting $\sigma$ of $S$ in each degree. The splittings do not commute with the differentials, and the difference is a $1$-cocycle `CochainComplex.cocycleOfDegreewiseSplit` from $X_3$ to $X_1$. Its morphism is `CochainComplex.homOfDegreewiseSplit` from $X_3$ to $X_1[1]$, and the triangle
$$X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3 \to X_1[1]$$
is `CochainComplex.triangleOfDegreewiseSplit`. Its image in the homotopy category is `CochainComplex.trianglehOfDegreewiseSplit`. The main results:

| Lean name | Statement |
|---|---|
| `CochainComplex.trianglehOfDegreewiseSplit_distinguished` | the triangle is distinguished in the homotopy category |
| `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` | a triangle is distinguished iff it is isomorphic to such a triangle |
| `CochainComplex.mappingConeHomOfDegreewiseSplitIso` | the mapping cone of the connecting morphism is isomorphic to $X_2[1]$ |
| `CochainComplex.homotopyEquivalences_shortComplexF_iff_of_splitting` | $f$ is a homotopy equivalence iff $X_3$ is contractible |
| `CochainComplex.homotopyEquivalences_shortComplexG_iff_of_splitting` | $g$ is a homotopy equivalence iff $X_1$ is contractible |

The module `Mathlib.Algebra.Homology.HomotopyCategory.ChainComplex` proves the same two statements for chain complexes on $\mathbb{N}$, in `ChainComplex.homotopyEquivalences_shortComplexF_iff_of_degreewiseSplit` and `ChainComplex.homotopyEquivalences_shortComplexG_iff_of_degreewiseSplit`.

#### Short exact sequences that do not split

For any short complex $S$ of cochain complexes, `CochainComplex.mappingCone.descShortComplex` is the morphism from the mapping cone of $f$ to $X_3$ that is $g$ on $X_2$ and zero on $X_1[1]$. The lemma `CochainComplex.mappingCone.inr_descShortComplex` says that it restricts to $g$, and `CochainComplex.mappingCone.descShortComplex_naturality` gives its naturality. In an abelian category, `CochainComplex.mappingCone.quasiIso_descShortComplex` says that it is a quasi-isomorphism when $S$ is short exact. The lemma `CochainComplex.mappingCone.homologySequenceδ_triangleh` compares the connecting map of the cone triangle with the connecting map of the long exact sequence of $S$.

#### Shifts and homology

The module `Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence` makes the homology functors a shift sequence: the homology in degree $a$ of $K[n]$ is the homology of $K$ in degree $n + a$, through `CochainComplex.ShiftSequence.shiftIso`. The isomorphism `CochainComplex.shiftShortComplexFunctorIso` identifies the short complex of $K[n]$ at $i$ with the short complex of $K$ at $n + i$, with the sign $(-1)^n$ on the outer terms. The consequences are:

| Lean name | Statement |
|---|---|
| `CochainComplex.quasiIso_shift_iff` | $\varphi[n]$ is a quasi-isomorphism iff $\varphi$ is one |
| `CochainComplex.quasiIsoAt_shift_iff` | the same at one degree, with $n + i = j$ |
| `CochainComplex.homologyFunctor_shift` | the shift of the homology functor in degree $0$ by $n$ is the homology functor in degree $n$ |
| `HomotopyCategory.shift_homologyFunctor` | the same in the homotopy category |

#### Single functors

The module `Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors` packages the functors `CochainComplex.singleFunctor` for all degrees as `CochainComplex.singleFunctors`, a family with isomorphisms between the shift of the single complex in degree $n$ and the single complex in another degree. The version `HomotopyCategory.singleFunctors` composes with the quotient, and `HomotopyCategory.singleFunctorPostcompQuotientIso` relates the two. Instances say that each single functor is additive, full and faithful.

#### Bounded below complexes up to homotopy

The object property `HomotopyCategory.plus` holds for the images of the bounded below complexes, by `HomotopyCategory.plus_quotient_obj_iff`. The category `HomotopyCategory.Plus` is its full subcategory. An instance says that it is triangulated, since the mapping cone of a map of bounded below complexes is bounded below by `CochainComplex.isStrictlyGE_mappingCone`. The related API:

| Lean name | Statement |
|---|---|
| `HomotopyCategory.Plus.ι` | the inclusion in the homotopy category, fully faithful by `HomotopyCategory.Plus.fullyFaithfulι` |
| `HomotopyCategory.Plus.quotient` | the quotient functor from `CochainComplex.Plus` |
| `HomotopyCategory.Plus.quotient_obj_surjective` | the quotient is surjective on objects |
| `HomotopyCategory.Plus.quasiIso` | the quasi-isomorphisms, with `HomotopyCategory.Plus.quasiIso_iff` |
| `HomotopyCategory.Plus.singleFunctor` | the single complexes as bounded below complexes |
| `CategoryTheory.Functor.mapHomotopyCategoryPlus` | the functor induced by an additive functor |

The lemmas `CochainComplex.plus_cylinder` and `CochainComplex.plus_pathObject` say that the cylinder and the path object of a bounded below complex are bounded below. So homotopies stay in the subcategory.

#### Common errors

1. The mapping cocone has the cochain `CochainComplex.mappingCocone.inr` of degree $1$, not $0$, because $L$ sits in the cocone with a shift. A lift into the cocone needs a $(-1)$-cochain to $L$, not a morphism.
2. `CochainComplex.mappingCone.descShortComplex` exists for every short complex, but it is a quasi-isomorphism only for a short exact sequence in an abelian category. It is not a homotopy equivalence in general, so the triangle it gives lives in the derived category and not in the homotopy category.
3. The triangle of a degreewise split sequence depends on the chosen splittings $\sigma$. Different splittings give homotopic connecting morphisms, but the triangles are not equal as terms.

### Exercises

1. (A) Write the objects and the differential of the mapping cocone of the identity of $K$, and show that it is contractible.
2. (A) For the split sequence $0 \to \mathbb{Z} \to \mathbb{Z} \oplus \mathbb{Z} \to \mathbb{Z} \to 0$ of single complexes in degree $0$, compute the cocycle of the splitting.
3. (B) Consider the short exact sequence $0 \to \mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \mathbb{Z}/2 \to 0$ of single complexes in degree $0$. Show that it is not split in degree $0$ and compute the mapping cone of the first map and the map to $\mathbb{Z}/2$.
4. (B) Prove that a morphism of complexes is a homotopy equivalence iff its shift by $n$ is one.
5. (B) Let $\varphi_0, \varphi_1 : F \to K$ be homotopic. Factor both maps through the path object with `HomologicalComplex.pathObject.lift`, and deduce that they are equal in the homotopy category when the path object map $\iota$ is a homotopy equivalence.
6. (C) Use `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` to show that a triangle of bounded below complexes is distinguished in `HomotopyCategory.Plus` iff it is distinguished in the homotopy category.

### Reference

<?reference?>
