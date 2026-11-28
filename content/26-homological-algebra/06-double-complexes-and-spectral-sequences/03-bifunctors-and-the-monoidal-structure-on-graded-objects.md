---
title: Bifunctors and the monoidal structure on graded objects
kind: api
modules:
  - Mathlib.CategoryTheory.GradedObject.Single
  - Mathlib.CategoryTheory.GradedObject.Bifunctor
  - Mathlib.CategoryTheory.GradedObject.Trifunctor
  - Mathlib.CategoryTheory.GradedObject.Associator
  - Mathlib.CategoryTheory.GradedObject.Unitor
  - Mathlib.CategoryTheory.GradedObject.Monoidal
  - Mathlib.CategoryTheory.GradedObject.Braiding
explains:
  E2: [CategoryTheory.GradedObject.single, CategoryTheory.GradedObject.mapBifunctor, CategoryTheory.GradedObject.mapBifunctorMapObj, CategoryTheory.GradedObject.mapTrifunctorMap, CategoryTheory.GradedObject.mapBifunctorAssociator, CategoryTheory.GradedObject.mapBifunctorLeftUnitor, CategoryTheory.GradedObject.HasTensor, CategoryTheory.GradedObject.Monoidal.tensorObj, CategoryTheory.GradedObject.monoidalCategory, CategoryTheory.GradedObject.Monoidal.braiding]
  E1: auto
families: []
requires: [V24.C04, V24.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bifunctors and the monoidal structure on graded objects

### Overview

A graded object of Section 1 is a family $X = (X_i)_{i \in I}$ of objects of a category $C$. A bifunctor $F : C_1 \times C_2 \to C_3$ acts on graded objects degreewise: from $X$ graded by $I$ and $Y$ graded by $J$ it gives the object graded by $I \times J$ with $F(X_i, Y_j)$ in degree $(i, j)$. With a map $p : I \times J \to K$ and the coproducts that it needs, the library sums these objects along the fibers of $p$. The result in degree $k$ is
$$\coprod_{p(i, j) = k} F(X_i, Y_j).$$

For a monoidal category $C$, an additive monoid $I$, the tensor product of $C$ as $F$ and the addition of $I$ as $p$, this gives the tensor product of graded objects, $(X \otimes Y)_n = \coprod_{i + j = n} X_i \otimes Y_j$. The unit is the unit of $C$ in degree $0$ and an initial object in the other degrees. The associator comes from a general associator for compositions of bifunctors, and the unitors from a general unitor. When $C$ has finite coproducts and its tensor product preserves them in each variable, graded objects indexed by $\mathbb{N}$ form a monoidal category. A braiding or a symmetry on $C$ gives one on graded objects.

These constructions are the base of the tensor product of complexes in Section 4.

### The library around it

#### Single graded objects

For an object $X$ of $C$ and $j \in J$, the graded object `CategoryTheory.GradedObject.single` $j$ applied to $X$ is $X$ in degree $j$ and an initial object in the other degrees. It needs `CategoryTheory.Limits.HasInitial` and decidable equality on $J$. The case $j = 0$ is `CategoryTheory.GradedObject.single₀`. The isomorphism `CategoryTheory.GradedObject.singleObjApplyIso` identifies the object in degree $j$ with $X$, and `CategoryTheory.GradedObject.isInitialSingleObjApply` says that the object in degree $i \neq j$ is initial. The natural isomorphism `CategoryTheory.GradedObject.singleCompEval` says that evaluation at $j$ after the single functor is the identity.

#### Bifunctors and trifunctors

The functor `CategoryTheory.GradedObject.mapBifunctor` $F$ $I$ $J$ sends $X$ and $Y$ to the graded object with $F(X_i, Y_j)$ in degree $(i, j)$. For $p : I \times J \to K$, the object `CategoryTheory.GradedObject.mapBifunctorMapObj` $F$ $p$ $X$ $Y$ is the image of this object under the map of graded objects of Section 1, so it exists under the condition `CategoryTheory.GradedObject.HasMap`. Its main data are:

| Lean name | Statement |
|---|---|
| `CategoryTheory.GradedObject.ιMapBifunctorMapObj` | the inclusion of $F(X_i, Y_j)$ for $p(i, j) = k$ |
| `CategoryTheory.GradedObject.mapBifunctorMapObjDesc` | a morphism out of degree $k$, from a morphism on each summand |
| `CategoryTheory.GradedObject.mapBifunctorMapObj_ext` | two morphisms out of degree $k$ are equal if they agree on each summand |
| `CategoryTheory.GradedObject.mapBifunctorMapMap` | the map induced by morphisms $X \to X'$ and $Y \to Y'$ |
| `CategoryTheory.GradedObject.mapBifunctorMap` | the bifunctor on graded objects, when all the coproducts exist |

The module `Mathlib.CategoryTheory.GradedObject.Trifunctor` does the same for a trifunctor. The functor `CategoryTheory.GradedObject.mapTrifunctor` gives the object graded by $I_1 \times I_2 \times I_3$, and `CategoryTheory.GradedObject.mapTrifunctorMap` sums it along a map $r : I_1 \times I_2 \times I_3 \to J$. A composition $G(F_{12}(X_1, X_2), X_3)$ of two bifunctors is a trifunctor. The structure `CategoryTheory.GradedObject.BifunctorComp₁₂IndexData` factors $r$ through an index type $I_{12}$ for the first two variables. The isomorphism `CategoryTheory.GradedObject.mapBifunctorComp₁₂MapObjIso` then identifies the iterated sum with the sum for the trifunctor. The condition `CategoryTheory.GradedObject.HasGoodTrifunctor₁₂Obj` says that the functor $G$ preserves the coproducts that the first step needs. The versions with index $23$ do the same for the last two variables.

#### Associator and unitors

The isomorphism `CategoryTheory.GradedObject.mapBifunctorAssociator` takes an isomorphism of trifunctors $G(F_{12}(X_1, X_2), X_3) \cong F(X_1, G_{23}(X_2, X_3))$ and index data for both sides. It gives an isomorphism between the two iterated sums of graded objects. The lemmas `CategoryTheory.GradedObject.ι_mapBifunctorAssociator_hom` and `CategoryTheory.GradedObject.ι_mapBifunctorAssociator_inv` compute it on each summand.

For a bifunctor $F$ and an object $X$ with $F(X, -) \cong \mathrm{id}$, and a map $p$ with $p(0, j) = j$, the isomorphism `CategoryTheory.GradedObject.mapBifunctorLeftUnitor` identifies the sum of $F$ applied to the single object $X$ in degree $0$ and $Y$ with $Y$. The construction needs $F(Z, -)$ to preserve initial objects for each $Z$, so that the summands outside degree $0$ are zero. The right form is `CategoryTheory.GradedObject.mapBifunctorRightUnitor`. The structure `CategoryTheory.GradedObject.TriangleIndexData` and the lemma `CategoryTheory.GradedObject.mapBifunctor_triangle` give the triangle identity for these unitors and the associator.

#### The tensor product of graded objects

Let $C$ be monoidal and $I$ an additive monoid. The condition `CategoryTheory.GradedObject.HasTensor` $X_1$ $X_2$ says that the coproducts of $X_1(i) \otimes X_2(j)$ over $i + j = n$ exist. Then `CategoryTheory.GradedObject.Monoidal.tensorObj` is the tensor product, with:

| Lean name | Statement |
|---|---|
| `CategoryTheory.GradedObject.Monoidal.ιTensorObj` | the inclusion of $X_1(i) \otimes X_2(j)$ for $i + j = n$ |
| `CategoryTheory.GradedObject.Monoidal.tensorObj_ext` | equality of morphisms out of the tensor product, summand by summand |
| `CategoryTheory.GradedObject.Monoidal.tensorHom` | the tensor product of two morphisms |
| `CategoryTheory.GradedObject.Monoidal.tensorUnit` | the unit of $C$ in degree $0$, an initial object elsewhere |
| `CategoryTheory.GradedObject.Monoidal.associator` | the associator, from `CategoryTheory.GradedObject.mapBifunctorAssociator` |
| `CategoryTheory.GradedObject.Monoidal.leftUnitor` | the left unitor, from `CategoryTheory.GradedObject.mapBifunctorLeftUnitor` |
| `CategoryTheory.GradedObject.Monoidal.pentagon` | the pentagon identity |

The associator needs the conditions `CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor` and `CategoryTheory.GradedObject.HasGoodTensorTensor₂₃`, which say that the tensor product preserves the coproducts that appear. The instance `CategoryTheory.GradedObject.monoidalCategory` assumes these conditions and a condition for the pentagon for all objects. For $I = \mathbb{N}$, each fiber of the addition is finite, so these conditions follow from finite coproducts in $C$ that the tensor product preserves in each variable.

For a braided category $C$, `CategoryTheory.GradedObject.Monoidal.braiding` is the isomorphism $X \otimes Y \cong Y \otimes X$, which exchanges the summands $X_i \otimes Y_j$ and $Y_j \otimes X_i$ with the braiding of $C$. The lemmas `CategoryTheory.GradedObject.Monoidal.hexagon_forward` and `CategoryTheory.GradedObject.Monoidal.hexagon_reverse` give the hexagon identities, and the instances `CategoryTheory.GradedObject.braidedCategory` and `CategoryTheory.GradedObject.symmetricCategory` give the structures. This braiding has no sign. The sign rule of the tensor product of complexes is in Section 4, and it does not come from these instances.

#### Common errors

1. `CategoryTheory.GradedObject.Monoidal.tensorObj` is defined only under `CategoryTheory.GradedObject.HasTensor`. For an index monoid with infinite fibers, such as $\mathbb{Z}$, the coproducts are infinite, so a category with only finite coproducts does not get the instance.
2. For $I = \mathbb{N}$, instance search finds the monoidal structure from `CategoryTheory.Limits.HasFiniteCoproducts` and `CategoryTheory.Limits.PreservesFiniteCoproducts` for the tensor product in each variable. This works only if the file imports `Mathlib.CategoryTheory.Limits.Preserves.Finite`; without it, the conditions `CategoryTheory.GradedObject.HasTensor` and the others are not found.

### Exercises

1. (A) For graded abelian groups indexed by $\mathbb{N}$, write the object in degree $2$ of $X \otimes Y$ as a direct sum of three groups.
2. (A) Use `CategoryTheory.GradedObject.singleObjApplyIso` and `CategoryTheory.GradedObject.isInitialSingleObjApply` to compute the tensor product of the single objects $\mathbb{Z}$ in degree $1$ and $\mathbb{Z}$ in degree $2$.
3. (B) For the index map $p : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ with $p(i, j) = \max(i, j)$, say which summands appear in degree $n$ of `CategoryTheory.GradedObject.mapBifunctorMapObj`, and whether they are finite in number.
4. (B) Show that the tensor unit is a unit up to isomorphism for graded abelian groups indexed by $\mathbb{N}$, by a direct computation in each degree.
5. (B) For graded vector spaces indexed by $\mathbb{N}$ with the braiding `CategoryTheory.GradedObject.Monoidal.braiding`, compute the map on $X_1 \otimes Y_1 \to Y_1 \otimes X_1$ and compare it with the Koszul sign rule.
6. (C) Explain why the condition `CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor` is needed for the associator: give the two iterated coproducts and the map that the tensor product must preserve.

### Reference

<?reference?>
