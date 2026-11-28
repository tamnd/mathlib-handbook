---
title: Presheaves of modules
kind: api
modules:
  - Mathlib.Algebra.Category.ModuleCat.Presheaf
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
  - Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
  - Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
  - Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
explains:
  E2: [PresheafOfModules, PresheafOfModules.instAbelian, PresheafOfModules.unitHomEquiv, PresheafOfModules.epi_iff_surjective, PresheafOfModules.freeAdjunction, PresheafOfModules.freeYoneda.isSeparating, PresheafOfModules.pushforward, PresheafOfModules.pullbackPushforwardAdjunction, PresheafOfModules.sheafificationAdjunction, PresheafOfModulesOfCommRing.monoidalCategory]
  E1: auto
families: []
requires: [V24.C02, V24.C03, V24.C04, V25.C06, V26.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Presheaves of modules

### Overview

Let $C$ be a category and let $R \colon C^{\mathrm{op}} \to \mathbf{Ring}$ be a presheaf of rings. A presheaf of modules over $R$ assigns to each object $X$ an $R(X)$-module $M(X)$, and to each map $f \colon Y \to X$ a restriction map $M(X) \to M(Y)$ that is linear along $R(f) \colon R(X) \to R(Y)$. The structure sheaf of a ringed space and the sheaf of a quasi-coherent module on a scheme are the main examples, before the sheaf condition. The category `PresheafOfModules R` is the setting of this chapter, and Section 2 passes to sheaves.

This section describes the category and its structure. It is abelian, with limits and colimits computed objectwise. It has free objects, a set of generators made from representable presheaves, and a tensor product when $R$ is commutative. A map of presheaves of rings gives restriction of scalars, a functor between sites gives pushforward and its left adjoint pullback, and a locally bijective map to a sheaf of rings gives sheafification. The section ends with the derivations of a map of presheaves of commutative rings and the presheaf of differentials.

### The library around it

#### The category of presheaves of modules

An object `M : PresheafOfModules R` has the field `M.obj X : ModuleCat (R.obj X)` for each `X : Cᵒᵖ`, and the field `M.map f` for each $f \colon X \to Y$ in $C^{\mathrm{op}}$, a linear map from `M.obj X` to the restriction of scalars of `M.obj Y` along `R.map f`. The axioms `PresheafOfModules.map_id` and `PresheafOfModules.map_comp` say that the maps `M.map f` are functorial. The compatibility with scalars is `PresheafOfModules.map_smul`:
$$M(f)(r \cdot m) = R(f)(r) \cdot M(f)(m).$$
A morphism $\varphi \colon M \to N$ is a family of linear maps `φ.app X` that commute with the restriction maps, by `PresheafOfModules.Hom.naturality`. Two morphisms are equal when their components are equal, `PresheafOfModules.hom_ext`. The constructor `PresheafOfModules.homMk` builds a morphism from a morphism of the underlying presheaves of groups that is linear on each object, and `PresheafOfModules.isoMk` builds an isomorphism from objectwise isomorphisms.

The functor `PresheafOfModules.toPresheaf R` forgets the scalars and keeps the presheaf of abelian groups. It is faithful and additive. The functor `PresheafOfModules.evaluation R X` takes the module at $X$. Another description is `PresheafOfModules.forgetToPresheafModuleCat`, which views $M$ as a presheaf of modules over the single ring $R(X)$ on the slice over $X$. The presheaf of rings itself is the unit object `PresheafOfModules.unit R`.

Sections are the global elements. The type `PresheafOfModules.sections M` has the families $(m_X)$ with $M(f)(m_X) = m_Y$ for each $f$, and `PresheafOfModules.unitHomEquiv` identifies these families with morphisms from the unit:
$$\operatorname{Hom}(R, M) \cong \operatorname{sections}(M).$$
Proof: a morphism $\varphi \colon R \to M$ gives the family $(\varphi_X(1))$, which is compatible because $\varphi$ is natural and the restriction maps of $R$ send $1$ to $1$. Conversely a compatible family $(m_X)$ gives $\varphi_X(r) = r \cdot m_X$, which is natural by `PresheafOfModules.map_smul`.

#### Limits, colimits and the abelian structure

Limits and colimits are computed objectwise. For a diagram $F \colon J \to$ `PresheafOfModules R`, the limit at $X$ is the limit of the modules $F(j)(X)$, and the restriction maps are induced by the universal property. The cone is `PresheafOfModules.limitCone` and `PresheafOfModules.isLimitLimitCone` proves the universal property. The same holds for colimits, with `PresheafOfModules.colimitCocone` and `PresheafOfModules.isColimitColimitCocone`. Hence the evaluation functors preserve limits and colimits, and they jointly reflect them, by `PresheafOfModules.evaluationJointlyReflectsLimits` and `PresheafOfModules.evaluationJointlyReflectsColimits`. The forgetful functor `PresheafOfModules.toPresheaf R` preserves both.

The abelian structure follows. The file `Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono` proves that a morphism is a monomorphism or an epimorphism exactly when each component is injective or surjective, by `PresheafOfModules.mono_iff_surjective` and `PresheafOfModules.epi_iff_surjective`. (The first name is a typo of the library: its statement is about injective components.) Proof for epimorphisms: the cokernel is computed objectwise, and $\varphi$ is an epimorphism if and only if its cokernel is zero, if and only if each component has zero cokernel. Then each monomorphism is the kernel of its cokernel, because this holds objectwise in each `ModuleCat (R.obj X)`. So the category is normal, `PresheafOfModules.instIsNormalMonoCategory` and `PresheafOfModules.instIsNormalEpiCategory`, and `PresheafOfModules.instAbelian` gives the abelian structure. Subobjects have the concrete form `PresheafOfModules.Submodule M`: a family of submodules $N(X) \subseteq M(X)$ that the restriction maps send into each other, by `PresheafOfModules.Submodule.map_mem`. The morphism `PresheafOfModules.Submodule.ι` is the inclusion.

#### Free presheaves of modules and generators

The file `Mathlib.Algebra.Category.ModuleCat.Presheaf.Free` defines the free functor `PresheafOfModules.free R`, from presheaves of types to presheaves of modules. The free presheaf on a presheaf of sets $P$ is $X \mapsto R(X)^{(P(X))}$, the free $R(X)$-module on $P(X)$. The adjunction `PresheafOfModules.freeAdjunction` says that it is left adjoint to the forgetful functor to presheaves of types. A morphism out of the free presheaf is determined by the images of the basis elements, by `PresheafOfModules.free_hom_ext`, and `PresheafOfModules.freeObjDesc` builds a morphism from a map of presheaves of sets.

The file `Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator` applies the free functor to the representable presheaves. For $X$ in $C$, the free presheaf on the Yoneda presheaf $\operatorname{Hom}(-, X)$ corepresents evaluation at $X$:
$$\operatorname{Hom}(\mathrm{free}(\operatorname{Hom}(-, X)), M) \cong M(X),$$
by `PresheafOfModules.freeYonedaEquiv`. This is the Yoneda lemma composed with the free adjunction. The class of these objects is `PresheafOfModules.freeYoneda R`. It is separating, `PresheafOfModules.freeYoneda.isSeparating`: two morphisms $M \rightrightarrows N$ that agree after each map from a free Yoneda object agree on each element of each $M(X)$. It is also detecting, `PresheafOfModules.freeYoneda.isDetecting`. When $C$ is small, the elements of $M$ give an epimorphism `PresheafOfModules.fromFreeYonedaCoproduct` from a coproduct of free Yoneda objects to $M$, and `PresheafOfModules.isColimitFreeYonedaCoproductsCokernelCofork` writes each presheaf of modules as a cokernel of a map between such coproducts. This is a presentation of $M$ by generators and relations.

#### Change of rings, pushforward and pullback

A morphism of presheaves of rings $\alpha \colon R \to R'$ gives restriction of scalars `PresheafOfModules.restrictScalars α`, from `PresheafOfModules R'` to `PresheafOfModules R`, objectwise along $\alpha_X$. It commutes with the forgetful functors, `PresheafOfModules.restrictScalarsCompToPresheaf`.

Let $F \colon C \to D$ be a functor, $R$ a presheaf of rings on $D$, $S$ a presheaf of rings on $C$, and $\varphi \colon S \to F^{\mathrm{op}} \circ R$ a morphism of presheaves of rings. The functor `PresheafOfModules.pushforward₀ F R` precomposes with $F^{\mathrm{op}}$, and `PresheafOfModules.pushforward φ` composes it with restriction along $\varphi$:
$$(\varphi_* M)(X) = M(F(X)) \text{ as an } S(X)\text{-module}.$$
For a continuous map of spaces $f \colon Y \to X$, with $F = f^{-1}$ on open sets, this is the direct image of sheaves of modules. The isomorphisms `PresheafOfModules.pushforwardId` and `PresheafOfModules.pushforwardComp` say that pushforward is functorial up to coherent isomorphism. When $R$ is a presheaf of commutative rings, `PresheafOfModules.pushforward₀` is a monoidal functor, by the file `Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal`.

The pullback `PresheafOfModules.pullback φ` is the left adjoint of the pushforward, with the adjunction `PresheafOfModules.pullbackPushforwardAdjunction`. The library defines it as a left adjoint, and does not give a formula. The existence uses the free Yoneda generators: the pushforward of $N$ followed by evaluation at $X$ is evaluation of $N$ at $F(X)$, so it is corepresented by a free Yoneda object, by `PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy`. The pullback is therefore defined on free Yoneda objects, and it extends to all objects because each object is a cokernel of a map between coproducts of these. The lemma `PresheafOfModules.pullbackObjIsDefined_eq_top` states that this works for all objects when the categories are small. Pullback is functorial up to isomorphism, by `PresheafOfModules.pullbackId` and `PresheafOfModules.pullbackComp`.

For a single ring, the file `Mathlib.Algebra.Category.ModuleCat.Pseudofunctor` collects the change of rings functors of Chapter 7 as pseudofunctors: `RingCat.moduleCatRestrictScalarsPseudofunctor` and `CommRingCat.moduleCatRestrictScalarsPseudofunctor` send a ring to its module category, contravariantly along restriction of scalars, and `CommRingCat.moduleCatExtendScalarsPseudofunctor` does it covariantly along extension of scalars. These pseudofunctors are the input of descent theory.

#### Presheaves over commutative rings and the tensor product

For a presheaf of commutative rings $R \colon C^{\mathrm{op}} \to \mathbf{CRing}$, the abbreviation `PresheafOfModulesOfCommRing R` is the category of presheaves of modules over the composite with the forgetful functor to rings. The file `Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing` gives the same constructions in this setting, such as `PresheafOfModulesOfCommRing.pushforward` and `PresheafOfModulesOfCommRing.pullback`. The file `Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal` defines the objectwise tensor product,
$$(M_1 \otimes M_2)(X) = M_1(X) \otimes_{R(X)} M_2(X),$$
with restriction maps $m_1 \otimes m_2 \mapsto M_1(f)(m_1) \otimes M_2(f)(m_2)$, by `PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul`. The instance `PresheafOfModulesOfCommRing.monoidalCategory` makes it a monoidal category, and `PresheafOfModulesOfCommRing.symmetricCategory` makes it symmetric. Tensoring with a fixed object preserves colimits, `PresheafOfModulesOfCommRing.instPreservesColimitsOfSizeTensorLeft`, because colimits are objectwise and the tensor product of modules preserves colimits in each variable.

#### Colimits over a cofiltered category and stalks

Let $C$ be a cofiltered category, such as the open neighborhoods of a point ordered by inclusion. The file `Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor` takes a colimit $R_\infty$ of the presheaf of rings $R$ and makes the colimit of the abelian groups $M(X)$ into an $R_\infty$-module, `PresheafOfModules.ModuleColimit`. The action is $[r] \cdot [m] = [r m]$, defined at a common stage, with `PresheafOfModules.ModuleColimit.smul_eq`. The result is a functor `PresheafOfModules.colimitFunctor` to `ModuleCat` of the colimit ring, left adjoint to the constant functor `PresheafOfModules.constFunctor`, by `PresheafOfModules.colimitAdjunction`. For a ringed space this is the stalk $M_x$ as a module over the local ring $\mathcal{O}_x$. Section 2 treats stalks of sheaves of modules.

#### Sheafification

Let $J$ be a Grothendieck topology on $C$, let $R$ be a sheaf of rings and let $\alpha \colon R_0 \to R$ be a morphism from a presheaf of rings that is locally injective and locally surjective, for example the identity, or the map from a presheaf of rings to its sheafification. The file `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify` takes a presheaf of $R_0$-modules $M_0$ and a sheafification $A$ of its underlying presheaf of groups, and gives $A$ the structure of a sheaf of $R$-modules, `PresheafOfModules.sheafify α φ`. Proof sketch of the action: for a section $r$ of $R$ and a section $a$ of $A$ over $X$, both are locally images of sections $r_0$ of $R_0$ and $m_0$ of $M_0$. The local products $r_0 m_0$ are compatible, so they glue to a section $r \cdot a$ of $A$, and the result does not depend on the choices. The structure `PresheafOfModules.Sheafify.SMulCandidate` carries this argument, and the module axioms, such as `PresheafOfModules.Sheafify.mul_smul`, follow by the same local argument.

The file `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` packages it as the functor `PresheafOfModules.sheafification α` from presheaves of $R_0$-modules to sheaves of $R$-modules. The adjunction `PresheafOfModules.sheafificationAdjunction` makes it left adjoint to the forgetful functor from sheaves of $R$-modules followed by restriction of scalars along $\alpha$. Its counit is an isomorphism, and it preserves finite limits, `PresheafOfModules.instPreservesFiniteLimitsSheafOfModulesSheafification`, because the sheafification of presheaves of abelian groups is exact.

#### Derivations and the presheaf of differentials

Let $\varphi \colon S \to F^{\mathrm{op}} \circ R$ be a map of presheaves of commutative rings, as for the pushforward, and let $M$ be a presheaf of $R$-modules. A derivation `PresheafOfModulesOfCommRing.Derivation M φ` is a family of derivations $d_X \colon R(X) \to M(X)$, relative to the ring maps of $\varphi$, that commute with the restriction maps. The Leibniz rule is `PresheafOfModulesOfCommRing.Derivation.d_mul`, and $d(1) = 0$ is `PresheafOfModulesOfCommRing.Derivation.d_one`. A derivation is universal, `PresheafOfModulesOfCommRing.Derivation.Universal`, when each derivation factors through it by a unique morphism of presheaves of modules. The class `PresheafOfModulesOfCommRing.HasDifferentials φ` says that a universal derivation exists.

For $F$ the identity and $\varphi' \colon S' \to R$, the construction `PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'` is the presheaf $X \mapsto \Omega_{R(X)/S'(X)}$, built from the Kähler differentials `CommRingCat.KaehlerDifferential` of Chapter 7, Section 10, with the restriction maps `CommRingCat.KaehlerDifferential.map`. The derivation `PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'` is universal, by `PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'`, so `PresheafOfModulesOfCommRing.DifferentialsConstruction.instHasDifferentials` holds. The general case of a functor $F$ is a TODO of the library.

#### Common errors

1. `PresheafOfModules R` needs a presheaf of rings with values in `RingCat`. For a presheaf of commutative rings, use `PresheafOfModulesOfCommRing R`, which inserts the forgetful functor, so that the tensor product instance applies.
2. The restriction map `M.map f` lands in the restriction of scalars of `M.obj Y`, not in `M.obj Y` as an `R.obj X`-module. Lemmas about the scalars need `PresheafOfModules.map_smul`.
3. The pullback functor is defined only as a left adjoint, with no objectwise formula. A computation of $\varphi^* M$ at an object must go through the adjunction `PresheafOfModules.pullbackPushforwardAdjunction`.

### Exercises

1. (A) For $C$ the category with one object and one map, show that `PresheafOfModules R` is the category of modules over the ring $R(\ast)$.
2. (A) Show that the kernel of a morphism of presheaves of modules is the family of kernels of its components, and that it is a `PresheafOfModules.Submodule`.
3. (B) Prove `PresheafOfModules.unitHomEquiv` in detail, and deduce that $\operatorname{Hom}(R, R)$ is the ring of global sections of $R$ when $C$ has a terminal object.
4. (B) Prove the bijection `PresheafOfModules.freeYonedaEquiv` from the Yoneda lemma and `PresheafOfModules.freeAdjunction`.
5. (B) For $C = \{U \subseteq V\}$ with one inclusion, describe a presheaf of modules as a module $M(V)$, a module $M(U)$ and a semilinear map. Compute the pullback along the inclusion of the full subcategory on $U$.
6. (C) Show that a morphism of presheaves of modules can be an epimorphism while its map on sections is not surjective. Hint: take a two point space and the sheaf of locally constant functions.

### Reference

<?reference?>
