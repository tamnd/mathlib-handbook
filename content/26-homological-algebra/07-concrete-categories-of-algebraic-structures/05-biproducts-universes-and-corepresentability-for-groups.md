---
title: Biproducts, universes and corepresentability for groups
kind: api
modules:
  - Mathlib.Algebra.Category.Grp.Biproducts
  - Mathlib.Algebra.Category.Grp.AB
  - Mathlib.Algebra.Category.Grp.Zero
  - Mathlib.Algebra.Category.Grp.Preadditive
  - Mathlib.Algebra.Category.Grp.LeftExactFunctor
  - Mathlib.Algebra.Category.Grp.EnoughInjectives
  - Mathlib.Algebra.Category.Grp.Injective
  - Mathlib.Algebra.Category.Grp.ZModuleEquivalence
  - Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
  - Mathlib.Algebra.Category.Grp.Yoneda
  - Mathlib.Algebra.Category.Grp.ForgetCorepresentable
  - Mathlib.Algebra.Category.MonCat.ForgetCorepresentable
  - Mathlib.Algebra.Category.MonCat.Yoneda
  - Mathlib.Algebra.Category.Grp.Ulift
  - Mathlib.Algebra.Category.Grp.Shrink
  - Mathlib.Algebra.Category.MonCat.Shrink
explains:
  E2: [AddCommGrpCat.biproductIsoPi, AddCommGrpCat.biprodIsoProd, AddCommGrpCat.isZero_iff_subsingleton, AddCommGrpCat.injective_of_divisible, Module.Baer.of_divisible, AddCommGrpCat.enoughInjectives, AddCommGrpCat.coyonedaObjIsoForget, AddCommGrpCat.leftExactFunctorForgetEquivalence]
  E1: auto
families: []
requires: [V24.C03, V24.C04, V24.C08, V25.C01, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Biproducts, universes and corepresentability for groups

### Overview

Section 1 proves that `AddCommGrpCat` is abelian. This section collects the files that make the abelian category of abelian groups usable: the additive structure on the morphisms, the zero object, the finite biproducts, the axioms AB4 and AB5 of Grothendieck, the injective objects and the enough injectives. These facts are the input to the derived functors of Chapter 4. A right derived functor of a functor out of $\mathbf{Ab}$ needs injective resolutions, and these exist because divisible groups are injective.

The section also treats three formal tools. The first is the equivalence between groups written multiplicatively and groups written additively, and between abelian groups and $\mathbb{Z}$-modules. The second is the corepresentability of the forgetful functors and the Yoneda functors with values in abelian groups. The third is the change of universe: the functors that lift a group to a larger universe or shrink it to a smaller one.

### The library around it

#### The preadditive structure

For abelian groups $M$ and $N$, the set $\operatorname{Hom}(M, N)$ is an abelian group under the pointwise sum $(f + g)(x) = f(x) + g(x)$. The file `Mathlib.Algebra.Category.Grp.Preadditive` gives the instances `AddCommGrpCat.instAddCommGroupHom` and `AddCommGrpCat.instPreadditive`. Composition is bilinear: $h \circ (f + g) = h \circ f + h \circ g$ because $h$ is additive, and $(f + g) \circ k = f \circ k + g \circ k$ by the pointwise definition. The simp lemmas `AddCommGrpCat.hom_add`, `AddCommGrpCat.hom_zero`, `AddCommGrpCat.hom_neg`, `AddCommGrpCat.hom_sub`, `AddCommGrpCat.hom_nsmul` and `AddCommGrpCat.hom_zsmul` move the operations through the wrapper `AddCommGrpCat.Hom.hom`, and `AddCommGrpCat.hom_add_apply` evaluates a sum at a point. The equivalence `AddCommGrpCat.homAddEquiv` identifies `M ⟶ N` with the group `M →+ N` as abelian groups.

#### Zero objects and biproducts

A group is a zero object of `GrpCat` exactly when it has one element. The file `Mathlib.Algebra.Category.Grp.Zero` proves `GrpCat.isZero_iff_subsingleton` and its versions `CommGrpCat.isZero_iff_subsingleton` and `AddCommGrpCat.isZero_iff_subsingleton`. Proof: the trivial group has exactly one map to each group and exactly one map from each group, so it is initial and terminal. Conversely, if $G$ is a zero object, then the identity of $G$ factors through the trivial group, so $G$ has one element. The instances `GrpCat.instHasZeroObject` and `AddCommGrpCat.hasZeroObject` follow.

In a preadditive category a finite product is a biproduct. The file `Mathlib.Algebra.Category.Grp.Biproducts` makes this concrete. `AddCommGrpCat.binaryProductLimitCone` is the product cone on $G \times H$, and `AddCommGrpCat.HasLimit.productLimitCone` is the product cone on $\prod_j f(j)$ for any family. The instances `AddCommGrpCat.instHasBinaryBiproducts` and `AddCommGrpCat.instHasFiniteBiproducts` follow. The two isomorphisms

| Lean name | Statement |
|---|---|
| `AddCommGrpCat.biprodIsoProd` | $G \oplus H \cong G \times H$ |
| `AddCommGrpCat.biproductIsoPi` | $\bigoplus_{j \in J} f(j) \cong \prod_{j \in J} f(j)$ for $J$ finite |

identify the abstract biproduct with the concrete product. The lemmas `AddCommGrpCat.biprodIsoProd_inv_comp_fst` and `AddCommGrpCat.biproductIsoPi_inv_comp_π` say that the inverse isomorphism followed by a biproduct projection is the coordinate projection. The proof of both isomorphisms is the uniqueness of limits: the biproduct is a product, the concrete cone is a product, and two limit cones of the same diagram are uniquely isomorphic.

#### The axioms of Grothendieck

The file `Mathlib.Algebra.Category.Grp.AB` proves that `AddCommGrpCat` satisfies the axioms AB4, AB4* and AB5, through the instances `instAB4AddCommGrpCat`, `instAB4StarAddCommGrpCat` and `instAB5AddCommGrpCat`. AB5 says that filtered colimits are exact. It follows from Section 4: a filtered colimit is computed on the underlying sets, and an element of the colimit has a representative at some stage, so the colimit of injective maps is injective. AB4 says that coproducts are exact, and AB4* says that products are exact, which is `instHasExactLimitsOfShapeDiscreteAddCommGrpCat`. The group $\mathbb{Z}$ is a separator, because a nonzero map $f \colon A \to B$ is nonzero on some element $a$, which is a map $\mathbb{Z} \to A$. This is `instHasSeparatorAddCommGrpCat`. With AB5 and a separator, `AddCommGrpCat` is a Grothendieck abelian category, `instIsGrothendieckAbelianAddCommGrpCat`.

#### Injective abelian groups

An abelian group $A$ is divisible if for each $a \in A$ and each $n \ge 1$ there is $b$ with $nb = a$. The groups $\mathbb{Q}$ and $\mathbb{Q}/\mathbb{Z}$ are divisible. The file `Mathlib.Algebra.Category.Grp.Injective` proves that a divisible group is injective in $\mathbf{Ab}$, with the instance `AddCommGrpCat.injective_of_divisible`.

Proof: by the criterion of Baer, it suffices to extend each homomorphism $\phi \colon I \to A$ from an ideal $I$ of $\mathbb{Z}$ to all of $\mathbb{Z}$. This is `Module.Baer.of_divisible`. Each ideal is $I = n\mathbb{Z}$. If $n = 0$, extend by $0$. Otherwise choose $b$ with $nb = \phi(n)$, and put $\psi(m) = mb$. Then $\psi(nk) = nkb = k\phi(n) = \phi(nk)$. So $\psi$ extends $\phi$. The criterion of Baer then gives injectivity in $\mathbb{Z}$-modules, and `AddCommGrpCat.injective_as_module_iff` transfers it to $\mathbf{Ab}$.

The file `Mathlib.Algebra.Category.Grp.EnoughInjectives` proves `AddCommGrpCat.enoughInjectives` and the multiplicative `CommGrpCat.enoughInjectives`. The embedding is
$$A \longrightarrow \prod_{\chi \in \operatorname{Hom}(A, \mathbb{Q}/\mathbb{Z})} \mathbb{Q}/\mathbb{Z}, \qquad a \mapsto (\chi(a))_\chi.$$
The target is a product of divisible groups, so it is divisible and injective. The map is injective because, for $a \neq 0$, the cyclic group $\langle a \rangle$ has a nonzero map to $\mathbb{Q}/\mathbb{Z}$, and this map extends to $A$ by injectivity of $\mathbb{Q}/\mathbb{Z}$.

#### Equivalences of presentation

The file `Mathlib.Algebra.Category.Grp.ZModuleEquivalence` proves that the forgetful functor from $\mathbb{Z}$-modules to abelian groups is an equivalence: the instances `ModuleCat.forget₂_addCommGroup_full`, `ModuleCat.forget₂_addCommGrp_essSurj` and `ModuleCat.forget₂AddCommGroupIsEquivalence`. Section 1 uses this to transfer the abelian structure. The file `Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup` gives the equivalences `groupAddGroupEquivalence : GrpCat ≌ AddGrpCat` and `commGroupAddCommGroupEquivalence`, built from the functors `GrpCat.toAddGrp`, `AddGrpCat.toGrp`, `CommGrpCat.toAddCommGrp` and `AddCommGrpCat.toCommGrp`. On objects they use the type synonyms `Additive` and `Multiplicative`, as `CommGrpCat.toAddCommGrp_obj_coe` states.

#### Corepresentability and Yoneda

The forgetful functor $U \colon \mathbf{Ab} \to \mathbf{Set}$ is corepresented by $\mathbb{Z}$: a homomorphism $\mathbb{Z} \to G$ is determined by the image of $1$, and each $g \in G$ is the image of $1$ for the map $n \mapsto ng$. So $U \cong \operatorname{Hom}(\mathbb{Z}, -)$. The file `Mathlib.Algebra.Category.Grp.ForgetCorepresentable` states this as `AddCommGrpCat.coyonedaObjIsoForget`, with `ULift ℤ` in place of $\mathbb{Z}$ so that the universes match. The group form of the bijection is `AddCommGrpCat.uliftZMultiplesAddEquiv`, and the bare bijection is `uliftZMultiplesHom`. The instances `AddCommGrpCat.forget_isCorepresentable`, `GrpCat.forget_isCorepresentable` and `CommGrpCat.forget_isCorepresentable` record the result. For monoids, the file `Mathlib.Algebra.Category.MonCat.ForgetCorepresentable` uses the free monoid on one generator, $\mathbb{N}$ written multiplicatively: `MonCat.coyonedaObjIsoForget` with the bijection `uliftPowersHom`, and `MonCat.forget_isCorepresentable`.

The files `Mathlib.Algebra.Category.Grp.Yoneda` and `Mathlib.Algebra.Category.MonCat.Yoneda` lift the Yoneda functor to values in groups. For abelian groups, $\operatorname{Hom}(M, N)$ is again an abelian group, so `AddCommGrpCat.coyoneda` is a functor $\mathbf{Ab}^{\mathrm{op}} \to \operatorname{Fun}(\mathbf{Ab}, \mathbf{Ab})$, with `AddCommGrpCat.coyoneda_obj_obj_coe` stating that its value is `M →+ N`. The variant `AddCommGrpCat.coyonedaType` sends a type $X$ and a group $G$ to the group of all functions $X \to G$. The isomorphism `AddCommGrpCat.coyonedaForget` says that `AddCommGrpCat.coyoneda` followed by the forgetful functor is the ordinary `CategoryTheory.coyoneda`. The same names exist for `CommGrpCat` and `CommMonCat`.

#### Left exact functors

Let $C$ be a preadditive category with finite biproducts. The file `Mathlib.Algebra.Category.Grp.LeftExactFunctor` proves that composition with the forgetful functor is an equivalence
$$\operatorname{Lex}(C, \mathbf{Ab}) \simeq \operatorname{Lex}(C, \mathbf{Set}),$$
which is `AddCommGrpCat.leftExactFunctorForgetEquivalence`. Proof sketch: each object of $C$ is canonically a commutative group object, through the diagonal and the sum of morphisms. A functor that preserves finite limits preserves group objects, and a commutative group object in $\mathbf{Set}$ is an abelian group. So a left exact $F \colon C \to \mathbf{Set}$ lifts to $\mathbf{Ab}$. The construction is `AddCommGrpCat.leftExactFunctorForgetEquivalence.inverse`, and the lift composed with the forgetful functor is $F$ again.

#### Changing the universe

The functor `GrpCat.uliftFunctor` sends a group in universe $u$ to its copy in universe $\max(u, v)$. The file `Mathlib.Algebra.Category.Grp.Ulift` proves that it is fully faithful, `GrpCat.uliftFunctorFullyFaithful`, that it preserves limits, `GrpCat.uliftFunctor_preservesLimitsOfSize`, and that it creates small limits, `GrpCat.instCreatesLimitsOfSizeUliftFunctor`. For abelian groups it is additive, `AddCommGrpCat.uliftFunctor_additive`, and it also preserves colimits, `AddCommGrpCat.instPreservesColimitsOfSizeUliftFunctor`. The colimit statement is the only one that is not formal, because colimits of groups are not computed on the sets. In the other direction, `GrpCat.shrinkFunctor` and `MonCat.shrinkFunctor` take a functor $C \to \mathbf{Grp}$ whose values are $w$-small and replace each value by an isomorphic group in universe $w$, with `GrpCat.shrinkFunctor_obj_coe` giving the carrier as a `Shrink` of the original.

#### Common errors

1. The sum `f + g` of morphisms in `AddCommGrpCat` is pointwise, but a goal about `(f + g).hom x` needs `AddCommGrpCat.hom_add` or `AddCommGrpCat.hom_add_apply` to unfold. The lemmas for `AddMonoidHom` do not fire on the wrapper.
2. `AddCommGrpCat.injective_of_divisible` is stated for a type with an instance `DivisibleBy A ℤ`. An object of the category needs this instance on its carrier before the instance search finds injectivity.
3. The corepresenting object of `forget AddCommGrpCat` is `ULift ℤ`, not `ℤ`, unless the universe is $0$. A statement written with `AddCommGrpCat.of ℤ` in a general universe does not typecheck.

### Exercises

1. (A) Prove that $\operatorname{Hom}(\mathbb{Z}/m, \mathbb{Z}/n) \cong \mathbb{Z}/\gcd(m, n)$ as abelian groups, with the pointwise sum of `AddCommGrpCat.instAddCommGroupHom`.
2. (A) Show that $\mathbb{Z}$ is not injective in $\mathbf{Ab}$, by extending the inclusion $2\mathbb{Z} \to \mathbb{Z}$.
3. (B) Prove that a quotient of a divisible group is divisible, and deduce that $\mathbb{Q}/\mathbb{Z}$ is injective.
4. (B) Show that infinite products in $\mathbf{Ab}$ are exact (AB4*) but that the inverse limit of a sequence $\cdots \to A_2 \to A_1$ is not exact in general.
5. (B) Use `AddCommGrpCat.coyonedaObjIsoForget` to show that a morphism $f$ of abelian groups is a monomorphism exactly when $f(a) = 0$ implies $a = 0$.
6. (C) Prove that $\mathbb{Q}/\mathbb{Z}$ is an injective cogenerator of $\mathbf{Ab}$, and that $\mathbb{Q}$ is injective but not a cogenerator. Hint: compute $\operatorname{Hom}(\mathbb{Z}/2, \mathbb{Q})$.

### Reference

<?reference?>
