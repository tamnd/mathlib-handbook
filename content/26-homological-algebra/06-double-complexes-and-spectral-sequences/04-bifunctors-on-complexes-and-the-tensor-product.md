---
title: Bifunctors on complexes and the tensor product
kind: api
modules:
  - Mathlib.Algebra.Homology.Bifunctor
  - Mathlib.Algebra.Homology.BifunctorFlip
  - Mathlib.Algebra.Homology.BifunctorHomotopy
  - Mathlib.Algebra.Homology.BifunctorAssociator
  - Mathlib.Algebra.Homology.BifunctorShift
  - Mathlib.Algebra.Homology.TotalComplexShift
  - Mathlib.Algebra.Homology.TotalComplexSymmetry
  - Mathlib.Algebra.Homology.Monoidal
explains:
  E2: [CategoryTheory.Functor.mapBifunctorHomologicalComplex, HomologicalComplex.HasMapBifunctor, HomologicalComplex.mapBifunctor, HomologicalComplex.mapBifunctorMapHomotopy₁, HomologicalComplex₂.totalFlipIso, HomologicalComplex.mapBifunctorFlipIso, HomologicalComplex.mapBifunctorAssociator, HomologicalComplex₂.totalShift₂Iso, CochainComplex.mapBifunctorShift₁Iso, HomologicalComplex.monoidalCategory]
  E1: auto
families: []
requires: [V24.C07, V25.C05, V26.C02, V26.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bifunctors on complexes and the tensor product

### Overview

Let $F : C_1 \times C_2 \to D$ be a bifunctor that is additive in each variable, for example the tensor product of modules. For complexes $K_1$ and $K_2$, the objects $F(K_1^p, K_2^q)$ form a bicomplex of Section 1, with the differentials $F(d, 1)$ and $F(1, d)$. Its total complex is the complex $F(K_1, K_2)$. For cochain complexes indexed by $\mathbb{Z}$ the differential on $F(K_1^p, K_2^q)$ is
$$d = F(d_{K_1}, 1) + (-1)^p F(1, d_{K_2}).$$
For the tensor product this is the tensor product of complexes, and its cohomology is the subject of the Künneth formula.

The section gives the basic properties of this construction. A homotopy in one variable gives a homotopy of the result. Exchange of the two variables gives an isomorphism, with signs that the complex shapes fix. Two compositions of bifunctors give isomorphic results when the shapes are associative. The construction commutes with the shift in each variable, but the two ways to shift both variables differ by the sign $(-1)^{xy}$. With a monoidal category $C$ and signs on the shape, the tensor product makes complexes a monoidal category. The construction uses the monoidal structure on graded objects of Section 3.

### The library around it

#### The bicomplex and the total complex

The functor `CategoryTheory.Functor.mapBifunctorHomologicalComplex` $F$ $c_1$ $c_2$ sends complexes of shapes $c_1$ and $c_2$ to the bicomplex of $F$. For a shape $c$ with `TotalComplexShape` $c_1$ $c_2$ $c$, the condition `HomologicalComplex.HasMapBifunctor` $K_1$ $K_2$ $F$ $c$ says that the bicomplex has a total complex. Then `HomologicalComplex.mapBifunctor` $K_1$ $K_2$ $F$ $c$ is this total complex. The main tools are:

| Lean name | Statement |
|---|---|
| `HomologicalComplex.ιMapBifunctor` | the inclusion of $F(K_1^{i_1}, K_2^{i_2})$ in the degree $j$ of the total complex |
| `HomologicalComplex.mapBifunctorDesc` | a morphism out of degree $j$, from one morphism for each summand |
| `HomologicalComplex.mapBifunctor.hom_ext` | two morphisms out of degree $j$ are equal if they agree on each summand |
| `HomologicalComplex.mapBifunctor.d_eq` | the differential is the sum of the two parts |
| `HomologicalComplex.mapBifunctorMap` | the morphism induced by morphisms $K_1 \to L_1$ and $K_2 \to L_2$ |

For cochain complexes indexed by $\mathbb{Z}$, the bifunctor `CategoryTheory.Functor.map₂CochainComplex` sends $K_1$ and $K_2$ to `CochainComplex.mapBifunctor` $K_1$ $K_2$ $F$, under the condition that the total complexes exist for all complexes. The general form for any shapes is `CategoryTheory.Functor.map₂HomologicalComplex`.

In degree $n$, the object of `CochainComplex.mapBifunctor` $K_1$ $K_2$ $F$ is the coproduct of the objects $F(K_1^p, K_2^q)$ over all pairs with $p + q = n$. For complexes that are bounded below, or bounded above, only a finite number of these objects are nonzero in each degree, so finite coproducts are sufficient. For unbounded complexes the coproducts are infinite, and the condition on total complexes must come from a category with countable coproducts, such as a category of modules. The differential on the summand of bidegree $(p, q)$ has two parts, one to the summand of bidegree $(p + 1, q)$ and one, with the sign $(-1)^p$, to the summand of bidegree $(p, q + 1)$.

#### Homotopies, symmetry and associativity

A homotopy $h$ from $f_1$ to $f_1'$ gives a homotopy from the map of $f_1$ and $f_2$ to the map of $f_1'$ and $f_2$. This is `HomologicalComplex.mapBifunctorMapHomotopy₁`, and `HomologicalComplex.mapBifunctorMapHomotopy₂` is the form for the second variable. So the construction passes to the homotopy categories of Chapter 3.

For a bicomplex $K$, the flipped bicomplex has the rows and the columns exchanged. When the shapes have a `TotalComplexShapeSymmetry`, the isomorphism `HomologicalComplex₂.totalFlipIso` identifies the total complex of the flipped bicomplex with the total complex of $K$. On the summand of bidegree $(i_1, i_2)$ it is the sign of the symmetry. The lemma `HomologicalComplex₂.flip_hasTotal_iff` says that the two total complexes exist together. For bifunctors, `HomologicalComplex.mapBifunctorFlipIso` is the isomorphism from the total complex of $F^{\mathrm{flip}}(K_2, K_1)$ to that of $F(K_1, K_2)$.

For three complexes and two compositions of bifunctors with an isomorphism $G(F_{12}(X_1, X_2), X_3) \cong F(X_1, G_{23}(X_2, X_3))$, the isomorphism `HomologicalComplex.mapBifunctorAssociator` is
$$G(F_{12}(K_1, K_2), K_3) \cong F(K_1, G_{23}(K_2, K_3)).$$
It needs the class `ComplexShape.Associative` on the six shapes, which fixes the signs, and the conditions `HomologicalComplex.HasGoodTrifunctor₁₂Obj` and `HomologicalComplex.HasGoodTrifunctor₂₃Obj`, which say that $G$ and $F$ preserve the coproducts of the inner total complexes. Its components are `HomologicalComplex.mapBifunctorAssociatorX`, which comes from `CategoryTheory.GradedObject.mapBifunctorAssociator` of Section 3.

#### Shifts

A bicomplex indexed by $\mathbb{Z} \times \mathbb{Z}$ has two shifts: `HomologicalComplex₂.shiftFunctor₁` shifts the first index and `HomologicalComplex₂.shiftFunctor₂` shifts the second index. Each changes the signs of the corresponding differentials. The total complex commutes with both shifts:

| Lean name | Statement |
|---|---|
| `HomologicalComplex₂.totalShift₁Iso` | the total complex of the first shift by $x$ is the shift by $x$ of the total complex, with no sign |
| `HomologicalComplex₂.totalShift₂Iso` | the same for the second shift by $y$, with the sign $(-1)^{py}$ on the summand of bidegree $(p, q)$ |
| `HomologicalComplex₂.totalShift₁Iso_trans_totalShift₂Iso` | the two ways to shift by $x$ and $y$ differ by the sign $(-1)^{xy}$ |

For bifunctors, `CochainComplex.mapBifunctorShift₁Iso` identifies $F(K_1[x], K_2)$ with $F(K_1, K_2)[x]$, and `CochainComplex.mapBifunctorShift₂Iso` identifies $F(K_1, K_2[y])$ with $F(K_1, K_2)[y]$. The lemma `CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso` gives the sign $(-1)^{xy}$, written `Int.negOnePow` of $x y$. The instance `CategoryTheory.Functor.instCommShift₂IntCochainComplexIntMap₂CochainComplex` puts these isomorphisms in the class `CategoryTheory.Functor.CommShift₂`.

#### The monoidal structure

Let $C$ be a monoidal preadditive category, $I$ an additive monoid and $c$ a shape on $I$ with the class `ComplexShape.TensorSigns`, which gives a sign `ComplexShape.ε` for each index. The tensor product `HomologicalComplex.tensorObj` is the total complex of the tensor product bifunctor, under the condition `HomologicalComplex.HasTensor`. The unit `HomologicalComplex.tensorUnit` is the unit of $C$ in degree $0$. The inclusions are `HomologicalComplex.ιTensorObj`, and the associator `HomologicalComplex.associator` and the unitors such as `HomologicalComplex.leftUnitor` are those of the graded objects, which commute with the differentials.

The instance `HomologicalComplex.monoidalCategory` needs a zero object, additive tensor products in each variable, and conditions on coproducts as in Section 3. The definition `HomologicalComplex.Monoidal.inducingFunctorData` transfers the axioms from graded objects through the faithful functor that forgets the differentials. A typical case is chain complexes indexed by $\mathbb{N}$ in an additive monoidal category with finite coproducts.

#### Common errors

1. The shift isomorphism in the second variable has a sign, and the one in the first variable has none. A proof that exchanges the order of two shifts must use `CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso` and carry the sign $(-1)^{xy}$.
2. `HomologicalComplex.mapBifunctor` needs the instance `HomologicalComplex.HasMapBifunctor`. For unbounded complexes indexed by $\mathbb{Z}$ the sums in each degree are infinite, so a category with only finite coproducts does not get it.
3. The isomorphism `HomologicalComplex.mapBifunctorFlipIso` is not the identity on the summands. It has the signs of `TotalComplexShapeSymmetry`, which are $(-1)^{pq}$ for cochain complexes indexed by $\mathbb{Z}$.

### Exercises

1. (A) For complexes of abelian groups $K_1$ and $K_2$ concentrated in degrees $0$ and $1$, write each object of the tensor product complex and its differential.
2. (A) Check that $d \circ d = 0$ for the differential $F(d, 1) + (-1)^p F(1, d)$, using that $F$ is additive in each variable.
3. (B) Use `HomologicalComplex.mapBifunctorMapHomotopy₁` to show that if $K_1$ is contractible, then the total complex of $F(K_1, K_2)$ is contractible.
4. (B) Verify the sign $(-1)^{xy}$ of `CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso` on the summand $F(K_1^p, K_2^q)$, from the signs of the two shift isomorphisms.
5. (B) Compute the tensor product of the complex $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ in degrees $-1$ and $0$ with itself, and its cohomology.
6. (C) Explain why the class `ComplexShape.Associative` is needed for `HomologicalComplex.mapBifunctorAssociator`: compare the signs of the two iterated total complexes on a summand of tridegree $(p, q, r)$.

### Reference

<?reference?>
