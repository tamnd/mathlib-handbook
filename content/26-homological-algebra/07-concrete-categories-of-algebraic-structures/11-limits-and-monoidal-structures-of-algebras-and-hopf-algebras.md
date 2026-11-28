---
title: Limits and monoidal structures of algebras and Hopf algebras
kind: api
modules:
  - Mathlib.Algebra.Category.AlgCat.FilteredColimits
  - Mathlib.Algebra.Category.AlgCat.Limits
  - Mathlib.Algebra.Category.AlgCat.Monoidal
  - Mathlib.Algebra.Category.AlgCat.Symmetric
  - Mathlib.Algebra.Category.AlgCat.TensorAlgebra
  - Mathlib.Algebra.Category.BialgCat.Monoidal
  - Mathlib.Algebra.Category.CoalgCat.Monoidal
  - Mathlib.Algebra.Category.CommAlgCat.FiniteType
  - Mathlib.Algebra.Category.CommAlgCat.Monoidal
  - Mathlib.Algebra.Category.CommBialgCat
  - Mathlib.Algebra.Category.CommHopfAlgCat
  - Mathlib.Algebra.Category.HopfAlgCat.Monoidal
explains:
  E2: [AlgCat.HasLimits.limitConeIsLimit, AlgCat.tensorAlgebraAdj, AlgCat.instSymmetricCategory, CoalgCat.instMonoidalCategory, BialgCat.instMonoidalCategory, CommAlgCat.binaryCofanIsColimit, CommAlgCat.instCartesianMonoidalCategoryOpposite, commBialgCatEquivComonCommAlgCat, commHopfAlgCatEquivCogrpCommAlgCat, instEssentiallySmallFGAlgCat]
  E1: auto
families: []
requires: [V24.C04, V24.C07, V08, V09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Limits and monoidal structures of algebras and Hopf algebras

### Overview

Section 3 defines the categories `AlgCat R`, `CommAlgCat R`, `CoalgCat R`, `BialgCat R` and `HopfAlgCat R` over a commutative ring $R$. This section describes their limits, filtered colimits and monoidal structures. The tensor product over $R$ is a symmetric monoidal structure on algebras, and it lifts to coalgebras, bialgebras and Hopf algebras. The tensor algebra is the free algebra on a module.

The main idea of the section is the dictionary with algebraic geometry. In `CommAlgCat R` the tensor product $A \otimes_R B$ is the coproduct. So the opposite category, the category of affine schemes over $R$, is cartesian monoidal, and a monoid object in it is the opposite of a commutative bialgebra. The files `Mathlib.Algebra.Category.CommBialgCat` and `Mathlib.Algebra.Category.CommHopfAlgCat` prove the two equivalences: commutative bialgebras are affine monoid schemes, and commutative Hopf algebras are affine group schemes.

### The library around it

#### Limits and filtered colimits of algebras

The file `Mathlib.Algebra.Category.AlgCat.Limits` computes limits in `AlgCat R` as for rings and modules. The subalgebra `AlgCat.sectionsSubalgebra F` of $\prod_j F(j)$ contains the compatible families, and the cone `AlgCat.HasLimits.limitCone F` on it is a limit by `AlgCat.HasLimits.limitConeIsLimit`. The forgetful functors to types, to rings and to modules preserve limits: `AlgCat.forget_preservesLimitsOfSize`, `AlgCat.forget₂Ring_preservesLimitsOfSize` and `AlgCat.forget₂Module_preservesLimitsOfSize`.

The file `Mathlib.Algebra.Category.AlgCat.FilteredColimits` shows that the forgetful functor to `RingCat` creates filtered colimits. A filtered colimit of $R$-algebras is the filtered colimit of the rings of Section 7, with the map from $R$ through any stage. The instance `instCreatesColimitsOfShapeAlgCatRingCatForget₂AlgHomCarrierRingHomCarrierOfIsFiltered` records this. So filtered colimits exist, and the forgetful functor to types preserves them.

#### The tensor algebra

The file `Mathlib.Algebra.Category.AlgCat.TensorAlgebra` defines the functor `AlgCat.tensorAlgebra R`, which sends a module $M$ to its tensor algebra
$$T(M) = R \oplus M \oplus (M \otimes M) \oplus (M \otimes M \otimes M) \oplus \cdots.$$
The adjunction `AlgCat.tensorAlgebraAdj` says that it is left adjoint to the forgetful functor from `AlgCat R` to `ModuleCat R`. Proof: an algebra map $T(M) \to A$ is determined by its restriction to $M$, because $M$ generates $T(M)$. Conversely a linear map $f \colon M \to A$ extends by $m_1 \otimes \dots \otimes m_n \mapsto f(m_1) \cdots f(m_n)$, which is multilinear. The unit is the inclusion $M \to T(M)$, by `AlgCat.tensorAlgebraAdj_unit_app`. The algebra of $T(M)$ is in Volume 8. The free algebra `AlgCat.free` of Section 3 is isomorphic to the tensor algebra of the free module, since both are left adjoint to the same forgetful functor to types.

#### The symmetric monoidal structure of algebras

The file `Mathlib.Algebra.Category.AlgCat.Monoidal` gives `AlgCat.instMonoidalCategory`: the tensor product of algebras $A \otimes_R B$, with $(a \otimes b)(a' \otimes b') = a a' \otimes b b'$, and the unit $R$. The structure isomorphisms are those of modules, by `AlgCat.hom_hom_associator`, `AlgCat.hom_hom_leftUnitor` and `AlgCat.hom_hom_rightUnitor`. The file `Mathlib.Algebra.Category.AlgCat.Symmetric` adds the braiding $a \otimes b \mapsto b \otimes a$, which is an algebra map, and `AlgCat.instSymmetricCategory`. The forgetful functor to `ModuleCat R` is braided monoidal.

The tensor product of algebras is not the coproduct of `AlgCat R` in general: the two maps $A \to A \otimes B$ and $B \to A \otimes B$ have commuting images, and a pair of algebra maps $A \to C$, $B \to C$ with images that do not commute does not factor. For commutative algebras this obstacle disappears, as the next part shows.

#### Coproducts of commutative algebras and the opposite category

The file `Mathlib.Algebra.Category.CommAlgCat.Monoidal` gives the tensor product on `CommAlgCat R`, `CommAlgCat.instMonoidalCategory`, and proves that it is the coproduct. The cofan `CommAlgCat.binaryCofan A B` has the maps $a \mapsto a \otimes 1$ and $b \mapsto 1 \otimes b$, and `CommAlgCat.binaryCofanIsColimit` proves the universal property, as for the pushout of Section 7. The ring $R$ is initial, `CommAlgCat.isInitialSelf`. A monoidal structure whose tensor product is the product and whose unit is terminal is cartesian. In the opposite category the tensor product is a product and $R$ is terminal, so `CommAlgCat.instCartesianMonoidalCategoryOpposite` holds. The opposite category is the category of affine schemes over $R$, and $\operatorname{Spec}(A \otimes_R B) = \operatorname{Spec} A \times_R \operatorname{Spec} B$.

#### Monoidal structures of coalgebras, bialgebras and Hopf algebras

For coalgebras $C$ and $D$, the tensor product $C \otimes_R D$ is a coalgebra with
$$\Delta(c \otimes d) = \sum c_{(1)} \otimes d_{(1)} \otimes c_{(2)} \otimes d_{(2)}, \qquad \varepsilon(c \otimes d) = \varepsilon(c) \varepsilon(d).$$
The file `Mathlib.Algebra.Category.CoalgCat.Monoidal` gives `CoalgCat.instMonoidalCategory`. The structure isomorphisms are the ones of modules, with `CoalgCat.associator_def` and the other `_def` lemmas. The axioms are not checked again: the structure is transported along the faithful forgetful functor to `ModuleCat R` with the tool `CategoryTheory.Monoidal.InducingFunctorData`, whose data for coalgebras is `CoalgCat.MonoidalCategory.inducingFunctorData`. The axioms of a monoidal category are equations between morphisms, and a faithful functor reflects them.

The same method gives `BialgCat.instMonoidalCategory`, through the forgetful functor to `AlgCat R` with `BialgCat.MonoidalCategory.inducingFunctorData`, and `HopfAlgCat.instMonoidalCategory`, through the forgetful functor to `BialgCat R`. The antipode of $H \otimes K$ is $S_H \otimes S_K$. The forgetful functors from bialgebras to algebras and to coalgebras are monoidal.

#### Commutative bialgebras and Hopf algebras as monoid and group objects

The file `Mathlib.Algebra.Category.CommBialgCat` defines `CommBialgCat R`, the category of bialgebras whose multiplication is commutative, with the pattern of Section 1. A commutative bialgebra $A$ gives the monoid object `CommAlgCat.monObjOpOf` on $\operatorname{Spec} A$ in the opposite category of `CommAlgCat R`. The multiplication is the opposite of $\Delta \colon A \to A \otimes A$ and the unit is the opposite of $\varepsilon \colon A \to R$, because the coproduct of the category is the tensor product. The axioms of a monoid object are the opposites of the axioms of a coalgebra. The equivalence `commBialgCatEquivComonCommAlgCat` states:
$$\mathbf{CommBialg}_R \simeq \operatorname{Mon}\bigl((\mathbf{CommAlg}_R)^{\mathrm{op}}\bigr)^{\mathrm{op}}.$$
A morphism of bialgebras gives a morphism of monoid objects, `instIsMonHomOppositeCommAlgCatOpOfHomToAlgHom`, and the inverse functor reads a bialgebra structure from a monoid object, by `instBialgebraCarrierUnopCommAlgCatOfMonObjOpposite`.

The file `Mathlib.Algebra.Category.CommHopfAlgCat` does the same for Hopf algebras. The antipode is the opposite of the inverse map of a group object, `CommAlgCat.grpObjOpOf`, and the equivalence is `commHopfAlgCatEquivCogrpCommAlgCat`:
$$\mathbf{CommHopf}_R \simeq \operatorname{Grp}\bigl((\mathbf{CommAlg}_R)^{\mathrm{op}}\bigr)^{\mathrm{op}}.$$
So a commutative Hopf algebra is an affine group scheme. For example, $R[t, t^{-1}]$ with $\Delta(t) = t \otimes t$ corresponds to the multiplicative group $\mathbb{G}_m$, and $R[t]$ with $\Delta(t) = t \otimes 1 + 1 \otimes t$ corresponds to the additive group $\mathbb{G}_a$. Cocommutative Hopf algebras correspond to commutative group objects. Monoid objects in a monoidal category are in Volume 24, Chapter 7.

#### Finitely generated commutative algebras

The file `Mathlib.Algebra.Category.CommAlgCat.FiniteType` defines `FGAlgCat R`, the full subcategory of `CommAlgCat R` on the algebras of finite type. The equivalence `FGAlgCat.equivUnder` identifies it with the ring maps $R \to S$ of finite type in `Under R`. The main result is `instEssentiallySmallFGAlgCat`: up to isomorphism, the algebras of finite type form a set. Proof: an algebra of finite type is a quotient $R[x_1, \dots, x_n] / I$. The structure `FGAlgCatSkeleton R` records the pair $(n, I)$, and `Algebra.FiniteType.exists_fgAlgCatSkeleton` says that each algebra of finite type is isomorphic to one of these quotients. The pairs form a type in the universe of $R$. The theorem `essentiallySmall_of_le` extends this to each class of ring maps of finite type, such as the étale maps. The same idea gives the essential smallness of rings of finite type in Section 7.

#### Common errors

1. In `AlgCat R` the tensor product is a monoidal structure, not the coproduct. Only in `CommAlgCat R` is $A \otimes_R B$ the coproduct.
2. `commBialgCatEquivComonCommAlgCat` goes to the opposite of a category of monoid objects in an opposite category. Two opposite steps appear, and a proof must apply `Opposite.unop` twice to reach an algebra.
3. The monoidal instances of `CoalgCat`, `BialgCat` and `HopfAlgCat` need a commutative ring $R$. The `_def` lemmas, such as `BialgCat.tensorObj_def`, state the structure in terms of the underlying modules, and simp uses them to compute.

### Exercises

1. (A) Show that the tensor algebra of the free module $R^n$ is the free algebra on $n$ generators.
2. (A) Give two algebra maps $\mathbb{Q}[x] \to M_2(\mathbb{Q})$ whose images do not commute, and deduce that $\mathbb{Q}[x] \otimes \mathbb{Q}[y]$ is not the coproduct of $\mathbb{Q}[x]$ and $\mathbb{Q}[y]$ in `AlgCat ℚ`.
3. (B) Check that $\Delta(t) = t \otimes t$, $\varepsilon(t) = 1$ and $S(t) = t^{-1}$ make $R[t, t^{-1}]$ a commutative Hopf algebra, and describe its group object under `commHopfAlgCatEquivCogrpCommAlgCat`.
4. (B) For the group algebra $k[G]$ of a finite group, describe the dual $\operatorname{Hom}_k(k[G], k) = k^G$ as a commutative Hopf algebra and its group scheme.
5. (B) Prove that the antipode of $H \otimes K$ is $S_H \otimes S_K$.
6. (C) Prove that $\operatorname{Hom}_{\mathbf{CommAlg}_R}(A, B)$ is a monoid for each commutative bialgebra $A$ and each commutative algebra $B$, using `CommAlgCat.monObjOpOf`.

### Reference

<?reference?>
