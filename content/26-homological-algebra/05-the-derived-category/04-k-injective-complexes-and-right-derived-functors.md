---
title: K-injective complexes and right derived functors
kind: api
modules:
  - Mathlib.Algebra.Homology.HomotopyCategory.KInjective
  - Mathlib.Algebra.Homology.HomotopyCategory.KProjective
  - Mathlib.Algebra.Homology.DerivedCategory.KInjective
  - Mathlib.Algebra.Homology.DerivedCategory.KProjective
  - Mathlib.Algebra.Homology.Factorizations.Basic
  - Mathlib.Algebra.Homology.Factorizations.CM5a
  - Mathlib.Algebra.Homology.Factorizations.CM5b
  - Mathlib.Algebra.Homology.ModelCategory.Lifting
  - Mathlib.Algebra.Homology.ModelCategory.Injective
  - Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
  - Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
  - Mathlib.Algebra.Homology.GrothendieckAbelian
explains:
  E2: [CochainComplex.IsKInjective, CochainComplex.isKInjective_of_injective, CochainComplex.IsKInjective.Qh_map_bijective, CochainComplex.IsKProjective, CochainComplex.degreewiseEpiWithInjectiveKernel, CochainComplex.cm5b, CochainComplex.Plus.modelCategoryQuillen.fibration_iff, HomotopyCategory.Plus.isRightDerivabilityStructure, CategoryTheory.Functor.rightDerivedFunctorPlus, HomologicalComplex.isGrothendieckAbelian]
  E1: auto
families: []
requires: [V25.C04, V25.C05, V26.C02, V26.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## K-injective complexes and right derived functors

### Overview

A morphism in the derived category is a fraction of morphisms of complexes, so it is difficult to compute directly. A cochain complex $L$ is K-injective if each morphism from an acyclic complex to $L$ is homotopic to zero. For such an $L$, the morphisms from any complex $K$ to $L$ in the derived category are the homotopy classes of morphisms of complexes. A bounded below complex of injective objects is K-injective. The dual notion is a K-projective complex.

The second part of the section shows that each bounded below complex in an abelian category with enough injectives is quasi-isomorphic to a bounded below complex of injective objects. The library obtains this from two factorization lemmas, and from them it builds the injective model structure of Quillen on bounded below complexes. The fibrant objects are the complexes of injective objects. The functor from bounded below complexes of injective objects to bounded below complexes is then a right derivability structure, and each additive functor $F$ gets a right derived functor $D^+(A) \to D^+(B)$ that is triangulated.

Throughout, $A$ and $B$ are abelian categories and complexes are indexed by $\mathbb{Z}$ with the shape `ComplexShape.up`, unless a statement says $\mathbb{N}$.

### The library around it

#### K-injective and K-projective complexes

The class `CochainComplex.IsKInjective` on a complex $L$ has one field, `CochainComplex.IsKInjective.nonempty_homotopy_zero`: for each acyclic $K$ and each $f : K \to L$ there is a homotopy from $f$ to $0$. The definition `CochainComplex.IsKInjective.homotopyZero` chooses this homotopy. The main results of the module `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` are:

| Lean name | Statement |
|---|---|
| `CochainComplex.isKInjective_iff_rightOrthogonal` | $L$ is K-injective iff its image in the homotopy category is right orthogonal to the acyclic complexes |
| `CochainComplex.isKInjective_of_injective` | a complex strictly zero below some degree $d$, with injective objects in each degree, is K-injective |
| `CochainComplex.isKInjective_shift_iff` | the shift $L[n]$ is K-injective iff $L$ is |
| `HomotopyEquiv.isKInjective` | a complex homotopy equivalent to a K-injective complex is K-injective |
| `CochainComplex.isKInjective_of_iso` | the same for an isomorphism of complexes |

The bound in `CochainComplex.isKInjective_of_injective` is necessary. An unbounded complex of injective objects can be acyclic and not contractible, and then the identity is not homotopic to zero. An instance gives the case of a complex indexed by $\mathbb{N}$ with injective objects, extended by zero to $\mathbb{Z}$.

The module `Mathlib.Algebra.Homology.HomotopyCategory.KProjective` has the duals: `CochainComplex.IsKProjective`, with morphisms from $K$ to acyclic complexes homotopic to zero, `CochainComplex.isKProjective_iff_leftOrthogonal`, and `CochainComplex.isKProjective_of_projective` for a complex strictly zero above some degree with projective objects. The lemma `CochainComplex.isKProjective_of_op` deduces K-projectivity from K-injectivity in the opposite category.

#### Morphisms in the derived category

The module `Mathlib.Algebra.Homology.DerivedCategory.KInjective` connects K-injective complexes with the derived category of Section 1:

| Lean name | Statement |
|---|---|
| `CochainComplex.IsKInjective.Qh_map_bijective` | for K-injective $L$, the map from morphisms $K \to L$ in the homotopy category to morphisms in the derived category is bijective |
| `CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective` | for K-injective $L$, cohomology classes of the Hom complex in degree $n$ are the shifted morphisms of degree $n$ from $K$ to $L$ |
| `CochainComplex.IsKInjective.quasiIso_iff` | a morphism between K-injective complexes is a quasi-isomorphism iff it is a homotopy equivalence |
| `CochainComplex.quasiIso_iff_of_injective` | the same for complexes indexed by $\mathbb{N}$ with injective objects |

The equivalence uses the Hom complex of Chapter 3, Section 3 and the shifted morphisms of Section 2. So for K-injective $L$, the group $\operatorname{Hom}_{D(A)}(K, L[n])$ is $H^n$ of the Hom complex. The module `Mathlib.Algebra.Homology.DerivedCategory.KProjective` gives the duals, for example `CochainComplex.IsKProjective.Qh_map_bijective` and `ChainComplex.quasiIso_iff_of_projective`.

#### Factorizations and the model structure

The class of morphisms `CochainComplex.degreewiseEpiWithInjectiveKernel` contains the morphisms that are epimorphisms in each degree with an injective kernel in each degree. Instances say that it is multiplicative and stable under retracts, and `CochainComplex.degreewiseEpiWithInjectiveKernel.epi` says that its morphisms are epimorphisms.

Let $A$ have enough injectives, and let $f : K \to L$ be a morphism where $K$ is strictly zero below $n + 1$ and $L$ is strictly zero below $n$. The two factorization lemmas are:

1. `CochainComplex.cm5b` gives $f = p \circ i$ with $i$ a monomorphism and $p$ a quasi-isomorphism in `CochainComplex.degreewiseEpiWithInjectiveKernel`. The middle complex is the mapping cone of the identity of a complex `CochainComplex.cm5b.I` of injective objects with zero differential, plus $L$. The definition `CochainComplex.cm5b.homotopyEquiv` shows that this sum is homotopy equivalent to $L$.
2. `CochainComplex.Plus.modelCategoryQuillen.cm5a` gives $f = \pi \circ \iota$ with $\iota$ a monomorphism and a quasi-isomorphism and $\pi$ in `CochainComplex.degreewiseEpiWithInjectiveKernel`. The case where $f$ is a monomorphism is `CochainComplex.Plus.modelCategoryQuillen.cm5a_cof`. The proof builds the middle complex as a limit of a sequence of complexes that is constant in each degree after a finite number of steps.

The module `Mathlib.Algebra.Homology.ModelCategory.Lifting` gives the lifting criterion. For a commutative square with $i$ on the left and $p$ on the right, let there be lifts in each degree, let $Q$ be the cokernel of $i$ and let $K$ be the kernel of $p$. Then the construction gives a cocycle of degree $1$ in the Hom complex from $Q$ to $K$, and `CochainComplex.Lifting.hasLift` says that the square has a lift if this cocycle is a coboundary.

With these results, `Mathlib.Algebra.Homology.ModelCategory.Injective` makes a model category on `CochainComplex.Plus` $A$. The model category structure `CochainComplex.Plus.modelCategoryQuillen.instModelCategory` is a scoped instance, so it is active only after `open CochainComplex.Plus.modelCategoryQuillen`. The classes are:

| Lean name | Statement |
|---|---|
| `CochainComplex.Plus.modelCategoryQuillen.weakEquivalence_iff` | the weak equivalences are the quasi-isomorphisms |
| `CochainComplex.Plus.modelCategoryQuillen.cofibration_iff` | the cofibrations are the monomorphisms |
| `CochainComplex.Plus.modelCategoryQuillen.fibration_iff` | the fibrations are the morphisms in `CochainComplex.degreewiseEpiWithInjectiveKernel` |
| `CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff` | a complex is fibrant iff its object in each degree is injective |

The general theory of model categories is in Volume 27.

#### The right derived functor

Let `CategoryTheory.InjectiveObject` $A$ be the full subcategory of injective objects, with inclusion `CategoryTheory.InjectiveObject.ι`. The localizer morphism `CochainComplex.Plus.localizerMorphism` is the functor from bounded below complexes of injective objects to bounded below complexes, with quasi-isomorphisms on both sides. The definition `CochainComplex.Plus.fibrantObjectEquivalence` identifies its source with the fibrant objects of the model category, and from this the library proves that it is a right derivability structure. The same holds for the homotopy categories, by `HomotopyCategory.Plus.isRightDerivabilityStructure` for `HomotopyCategory.Plus.localizerMorphism`. Two existence results follow:

1. `CochainComplex.Plus.exists_quasiIso_injective`: each complex strictly zero below $n$ has a quasi-isomorphism to a complex of injective objects strictly zero below $n$.
2. `DerivedCategory.Plus.exists_injective_nonempty_iso`: each object of $D^+(A)$ in $D^{\ge n}$ is the image of such a complex.

For an additive functor $F : A \to B$ and $A$ with enough injectives, `CategoryTheory.Functor.rightDerivedFunctorPlus` is a functor from `DerivedCategory.Plus` $A$ to `DerivedCategory.Plus` $B$. It is the right derived functor of the functor that $F$ induces on bounded below homotopy categories, with the unit `CategoryTheory.Functor.rightDerivedFunctorPlusUnith`. The unit `CategoryTheory.Functor.rightDerivedFunctorPlusUnit` from the category of complexes makes it a right derived functor of the functor on complexes too. Instances say that it commutes with the shift, that it is triangulated by `CategoryTheory.Functor.instIsTriangulatedPlusRightDerivedFunctorPlus`, and that the unit is an isomorphism on complexes of injective objects. A natural transformation $F \to G$ gives `CategoryTheory.NatTrans.rightDerivedFunctorPlus`, and the lemmas for sums, negation, the identity and composition make this map additive, as `CategoryTheory.NatTrans.rightDerivedFunctorPlusAddMonoidHom`.

#### Grothendieck abelian categories of complexes

The module `Mathlib.Algebra.Homology.GrothendieckAbelian` proves the instance `HomologicalComplex.isGrothendieckAbelian`. If $A$ is a Grothendieck abelian category, the shape $c$ has no loop and the index type is small, then the category of complexes of shape $c$ is Grothendieck abelian. The instances `HomologicalComplex.ab5OfSize` and `HomologicalComplex.hasExactColimitsOfShape` give the exactness of filtered colimits, and `HomologicalComplex.locallySmall` gives local smallness.

#### Common errors

1. `CochainComplex.isKInjective_of_injective` needs the instance `CochainComplex.IsStrictlyGE` for some degree $d$. A complex with injective objects in each degree and no bound does not get the class, and the statement is false for some such complexes.
2. The model structure on `CochainComplex.Plus` is a scoped instance. Without `open CochainComplex.Plus.modelCategoryQuillen`, the classes `HomotopicalAlgebra.Fibration` and `HomotopicalAlgebra.WeakEquivalence` do not find it.
3. `CategoryTheory.Functor.rightDerivedFunctorPlus` is a functor between bounded below derived categories, not between full derived categories. To apply it to an object of $A$, first send the object to `DerivedCategory.Plus` $A$ as a single complex.

### Exercises

1. (A) Show that the zero complex is K-injective, from the definition of `CochainComplex.IsKInjective`.
2. (A) Use `CochainComplex.isKInjective_of_injective` and `CochainComplex.isKInjective_shift_iff` to show that the shift of a bounded below complex of injective objects is K-injective.
3. (B) Show that an acyclic K-injective complex is contractible: apply the definition to its identity.
4. (B) Over the ring $\mathbb{Z}/4$, the module $\mathbb{Z}/4$ is injective. Show that the unbounded complex with $\mathbb{Z}/4$ in each degree and multiplication by $2$ as each differential is acyclic but not contractible, so that it is not K-injective.
5. (B) For K-injective $L$ and any complex $K$, deduce from `CochainComplex.IsKInjective.Qh_map_bijective` that a morphism $K \to L$ of complexes is zero in the derived category iff it is homotopic to zero.
6. (C) Let $F$ be additive and let $X$ be an injective object of $A$. Use the unit `CategoryTheory.Functor.rightDerivedFunctorPlusUnit` to show that the right derived functor sends the single complex $X$ in degree $0$ to the single complex $F(X)$ in degree $0$.

### Reference

<?reference?>
