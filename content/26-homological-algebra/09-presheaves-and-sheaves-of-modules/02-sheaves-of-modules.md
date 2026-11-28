---
title: Sheaves of modules
kind: api
modules:
  - Mathlib.Algebra.Category.ModuleCat.Sheaf
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
  - Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
  - Mathlib.Algebra.Category.ModuleCat.Stalk
explains:
  E2: [SheafOfModules, SheafOfModules.instAbelian, SheafOfModules.freeHomEquiv, SheafOfModules.GeneratingSections, SheafOfModules.IsFiniteType, SheafOfModules.IsQuasicoherent, SheafOfModules.IsLocallyFree, SheafOfModules.pullbackPushforwardAdjunction, SheafOfModules.Submodule, PresheafOfModules.germ_smul]
  E1: auto
families: []
requires: [V24.C04, V25.C02, V25.C04, V25.C06, V26.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sheaves of modules

### Overview

Let $J$ be a Grothendieck topology on a category $C$ and let $R$ be a sheaf of rings for $J$. A sheaf of modules over $R$ is a presheaf of modules over the underlying presheaf of rings of $R$ whose underlying presheaf of abelian groups is a sheaf. This is the setting of quasicoherent sheaves on a scheme, of vector bundles on a manifold, and of modules over a ringed topos.

This section describes the category `SheafOfModules R` and its structure. It is a full subcategory of the presheaves of modules of Section 1. It is abelian, it has limits and colimits, and sheafification is a localization functor onto it. It has free objects and sections, so generators and presentations make sense. With these, the library defines sheaves of finite type, quasicoherent sheaves, sheaves of finite presentation and locally free sheaves. A continuous functor between sites and a map of sheaves of rings give a pushforward and a pullback. The last file puts a module structure on the stalks of a presheaf of modules on a topological space.

### The library around it

#### The category

The structure `SheafOfModules R` has two fields: `SheafOfModules.val`, a presheaf of modules over the underlying presheaf of rings of $R$, and `SheafOfModules.isSheaf`, the sheaf condition for its underlying presheaf of abelian groups. A morphism is a structure `SheafOfModules.Hom` with one field `SheafOfModules.Hom.val`, a morphism of presheaves of modules. Two morphisms are equal when their values are equal, by `SheafOfModules.hom_ext`.

The forgetful functor `SheafOfModules.forget` to `PresheafOfModules R.obj` is fully faithful, by `SheafOfModules.fullyFaithfulForget`. So it reflects isomorphisms, and the study of a morphism of sheaves can often move to presheaves. The other functors out of the category are:

| Lean name | Target |
|---|---|
| `SheafOfModules.evaluation` | the module of sections over one object $X$ |
| `SheafOfModules.toSheaf` | the sheaf of abelian groups |
| `SheafOfModules.forgetToSheafModuleCat` | a sheaf of modules over the ring of an initial object |
| `SheafOfModules.sectionsFunctor` | the type of global sections |

Morphisms form an abelian group, and `SheafOfModules.instPreadditive` makes the category preadditive. The unit object `SheafOfModules.unit R` is $R$ as a module over itself. Maps from it are global sections: `SheafOfModules.unitHomEquiv` is a bijection from `unit R ⟶ M` to the global sections `SheafOfModules.sections M`.

The comparison with presheaves uses two local conditions on a map $f$ of presheaves of modules, `PresheafOfModules.IsLocallySurjective` and `PresheafOfModules.IsLocallyInjective`. When $f \colon M_1 \to M_2$ is locally bijective and $N$ is a sheaf, `PresheafOfModules.homEquivOfIsLocallyBijective` says that composition with $f$ is a bijection from maps $M_2 \to N$ to maps $M_1 \to N$. Proof idea: this holds for the underlying presheaves of abelian groups, by the theory of Volume 25. The map of abelian groups that it gives is linear, because linearity is a local property and $N$ is separated.

#### Abelian structure, limits and colimits

Limits in `SheafOfModules R` are limits of presheaves of modules. The instance `SheafOfModules.createsLimit` says that the forgetful functor creates limits, so `SheafOfModules.hasLimitsOfSize` holds and evaluation at each object preserves limits. The reason is `PresheafOfModules.isSheaf_of_isLimit`: a limit of sheaves, computed objectwise, is a sheaf, because the sheaf condition is itself a limit condition.

Colimits need sheafification, because a cokernel of sheaves, computed in presheaves, is not a sheaf in general. The file `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits` takes a colimit in presheaves and applies the sheafification functor of Section 1. Since this functor is a left adjoint, it preserves colimits, and since the forgetful functor is fully faithful, the result is a colimit of sheaves. The instance needs `HasWeakSheafify J AddCommGrpCat` and `J.WEqualsLocallyBijective AddCommGrpCat`.

The instance `SheafOfModules.instAbelian` makes `SheafOfModules R` abelian under `HasSheafify J AddCommGrpCat` and the same condition on locally bijective maps. Proof sketch: the presheaves of modules form an abelian category, the sheaves form a full subcategory closed under finite limits, and the inclusion has a left adjoint, the sheafification, that preserves finite limits. A full subcategory with these properties is abelian. When $C$ is small and the universes agree, the instance applies with no extra hypothesis.

The file `Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization` gives the precise form of the last argument. The instance `PresheafOfModules.instIsLocalizationSheafOfModulesSheafificationInverseImageFunctorOppositeAbWToPresheaf` says that `PresheafOfModules.sheafification α` is a localization functor, in the sense of Volume 25, Chapter 4. It inverts exactly the maps whose underlying map of presheaves of abelian groups is in `CategoryTheory.GrothendieckTopology.W`, by `PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`.

#### Change of rings

A map $\alpha \colon R \to R'$ of sheaves of rings on the same site gives the restriction of scalars `SheafOfModules.restrictScalars α`, from sheaves of $R'$-modules to sheaves of $R$-modules. It does not change the underlying sheaf of abelian groups, so the sheaf condition is kept. When $\alpha$ is locally surjective and the target is a sheaf, `PresheafOfModules.restrictHomEquivOfIsLocallySurjective` says that restriction of scalars is a bijection on morphisms. The reason is that a map that is $R$-linear is then locally $R'$-linear, and $R'$-linearity is a local condition.

#### Free sheaves and generators

From here on the universe of the modules is the universe of the rings. For a type $I$, the free sheaf `SheafOfModules.free I` is the coproduct of $I$ copies of `unit R`, with the inclusions `SheafOfModules.ιFree i` and the colimit cofan `SheafOfModules.isColimitFreeCofan`. The map out of it is a family of sections:
$$\operatorname{Hom}(\mathrm{free}\ I, M) \cong (I \to \Gamma(M)),$$
which is `SheafOfModules.freeHomEquiv M`. The section that goes with $i$ is `SheafOfModules.freeSection i`. The free construction is a functor `SheafOfModules.freeFunctor` on types, it preserves colimits, and `SheafOfModules.freeSumIso` identifies the free sheaf on $I \oplus I'$ with a binary coproduct. A functor $F$ between categories of sheaves of modules with an isomorphism $F(\mathrm{unit}) \cong \mathrm{unit}$ and that preserves coproducts sends free sheaves to free sheaves, by `SheafOfModules.mapFreeIso`.

A structure `SheafOfModules.GeneratingSections M` is a type $I$ with a family $s \colon I \to \Gamma(M)$ such that the map `SheafOfModules.GeneratingSections.π` from `free I` to $M$ is an epimorphism. An epimorphism $M \to N$ moves generators of $M$ to generators of $N$, by `SheafOfModules.GeneratingSections.ofEpi`. The family is of finite type, `SheafOfModules.GeneratingSections.IsFiniteType`, when $I$ is finite.

Global generators are rare. A sheaf on a scheme need not have enough global sections. So the useful notion is local. A structure `SheafOfModules.LocalGeneratorsData M` is a family of objects $X_i$ that covers the terminal object, `SheafOfModules.LocalGeneratorsData.coversTop`, with generating sections of the restriction `M.over (X i)` for each $i$. Here `SheafOfModules.over` restricts a sheaf of modules to the slice site over $X$. The class `SheafOfModules.IsFiniteType M` says that such data exists with each index type finite, and `SheafOfModules.IsFiniteType.exists_localGeneratorsData` gives it.

#### Quasicoherent and locally free sheaves

A structure `SheafOfModules.Presentation M` has generators of $M$ and generators of the kernel of their map $\pi$:
$$\mathrm{free}\ I' \to \mathrm{free}\ I \to M \to 0.$$
So $M$ is a cokernel of a map of free sheaves, by `SheafOfModules.Presentation.isColimit`. Conversely, `SheafOfModules.presentationOfIsCokernelFree` makes a presentation from such a cokernel. A presentation is finite, `SheafOfModules.Presentation.IsFinite`, when both index types are finite.

A structure `SheafOfModules.QuasicoherentData M` is a cover $X_i$ of the terminal object with a presentation of each `M.over (X i)`. The class `SheafOfModules.IsQuasicoherent M` says that such data exists, and `SheafOfModules.IsFinitePresentation M` asks for finite presentations. This is the definition of the Stacks project for a ringed site: locally, $M$ is a cokernel of a map of free modules. Each sheaf of finite presentation is quasicoherent and of finite type, by the instances `SheafOfModules.instIsQuasicoherentOfIsFinitePresentation` and `SheafOfModules.instIsFiniteTypeOfIsFinitePresentation`. Restriction to a slice keeps the property, by `SheafOfModules.isQuasicoherent_over`, and so does a pushforward along a left adjoint functor of sites, by `SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint`.

A sheaf is locally free when it is locally isomorphic to a free sheaf. The class `SheafOfModules.LocalGeneratorsData.IsLocallyFreeData` asks that each map $\pi$ of local generators is an isomorphism, and `SheafOfModules.IsLocallyFree M` asks that such data exists. A free sheaf is locally free, by `SheafOfModules.instIsLocallyFreeFree`, with the generators `SheafOfModules.free.generatingSections`. A locally free sheaf is quasicoherent, by `SheafOfModules.instIsQuasicoherentOfIsLocallyFree`: its local presentations have no relations.

#### Pushforward and pullback

Let $F \colon C \to D$ be a continuous functor from a site $(C, J)$ to a site $(D, K)$. Let $S$ be a sheaf of rings on $C$, $R$ a sheaf of rings on $D$, and $\varphi$ a map from $S$ to the pushforward of $R$, made with `CategoryTheory.Functor.sheafPushforwardContinuous`. The functor `SheafOfModules.pushforward φ` sends a sheaf of $R$-modules $M$ to $M \circ F^{\mathrm{op}}$, a sheaf of $S$-modules by restriction of scalars along $\varphi$. It is compatible with identities and compositions, by `SheafOfModules.pushforwardId` and `SheafOfModules.pushforwardComp`. An adjunction $F \dashv G$ of sites gives an adjunction of pushforwards, `SheafOfModules.pushforwardPushforwardAdj`, and an equivalence of sites gives `SheafOfModules.pushforwardPushforwardEquivalence`. The slice functors `SheafOfModules.overMap` and `SheafOfModules.overPullback` are special pushforwards.

The pullback `SheafOfModules.pullback φ` is defined as the left adjoint of the pushforward, when it exists, and `SheafOfModules.pullbackPushforwardAdjunction` is the adjunction. It exists when the pushforward of presheaves of modules is a right adjoint and sheafification exists on $D$. The construction `SheafOfModules.PullbackConstruction.adjunction` forgets to presheaves, takes the presheaf pullback of Section 1, and sheafifies. The isomorphism `SheafOfModules.pullbackIso` identifies `pullback φ` with this composite, and `SheafOfModules.sheafificationCompPullback` says that pullback commutes with sheafification. The pseudofunctor laws `SheafOfModules.pullbackId` and `SheafOfModules.pullbackComp` follow from those of the pushforward, by uniqueness of adjoints.

The unit object corresponds under the adjunction to `SheafOfModules.unitToPushforwardObjUnit φ`. Its adjoint map `SheafOfModules.pullbackObjUnitToUnit φ` is an isomorphism when $F$ is a final functor. Since the pullback is a left adjoint, it preserves coproducts, so `SheafOfModules.pullbackObjFreeIso` gives an isomorphism from the pullback of `free I` to `free I`. So pullback keeps generators and presentations, and hence finite type and quasicoherence, once the cover is moved along $F$.

#### Subsheaves of modules

A structure `SheafOfModules.Submodule M` is a submodule of the presheaf of modules `SheafOfModules.val M` whose membership is local: a section is in it when its restrictions to a covering family are in it. The sheaf condition holds for such a submodule, so `SheafOfModules.Submodule.toSheafOfModules` is a sheaf of modules with the monomorphism `SheafOfModules.Submodule.ι` into $M$. The submodules form a complete lattice, `SheafOfModules.Submodule.instCompleteLattice`. The infimum is computed as the infimum of presheaf submodules, by `SheafOfModules.Submodule.toSubmodule_sInf`, since an intersection of local conditions is local.

#### Stalks

Let $X$ be a topological space, $R$ a presheaf of rings on $X$ and $M$ a presheaf of modules over $R$. The stalk $M_x$ is the colimit of the abelian groups $M(U)$ over the open neighborhoods $U$ of $x$, and $R_x$ is the colimit of the rings $R(U)$. The file `Mathlib.Algebra.Category.ModuleCat.Stalk` gives $M_x$ an $R_x$-module structure, both for `RingCat` and for `CommRingCat` values. The key lemma is `PresheafOfModules.germ_smul`:
$$\operatorname{germ}_x(r \cdot m) = \operatorname{germ}_x(r) \cdot \operatorname{germ}_x(m)$$
for $r \in R(U)$ and $m \in M(U)$, with `TopCat.Presheaf.germ`. The general construction is `CategoryTheory.Limits.IsColimit.module`: for a filtered diagram of rings and a compatible diagram of modules, the colimit of the modules is a module over the colimit of the rings, with `CategoryTheory.Limits.IsColimit.ι_smul` as its defining property. Proof idea: two germs have representatives on a common neighborhood, because the diagram is filtered. Multiply there and take the germ. The result does not depend on the representatives, because two choices agree on a smaller neighborhood.

#### Common errors

1. A cokernel in `SheafOfModules R` is the sheafification of the presheaf cokernel. Its sections over $X$ are not the quotient $M(X) / f(N(X))$ in general, so evaluation does not preserve cokernels.
2. The sheaf condition of `SheafOfModules` is on the underlying presheaf of abelian groups. A proof that $M$ is a sheaf must give `Presheaf.IsSheaf J M.presheaf`, not a sheaf condition for a presheaf of modules.
3. `SheafOfModules.IsQuasicoherent` uses covers of the terminal object of $C$. On a site with no terminal object, the condition `CategoryTheory.GrothendieckTopology.CoversTop` still makes sense, but the slices `M.over (X i)` are the correct place for the presentations, not the sections $M(X_i)$.

### Exercises

1. (A) Show that `SheafOfModules.unit R` is quasicoherent and of finite presentation, with $I = \{\ast\}$ and no relations.
2. (A) Let $f \colon M \to N$ be a morphism of sheaves of modules. Show that $f$ is a monomorphism if and only if each map $M(X) \to N(X)$ is injective.
3. (B) On the space $X = \{a, b\}$ with the discrete topology, describe sheaves of modules over the constant sheaf of rings $\mathbb{Z}$, and show that the category is equivalent to pairs of abelian groups.
4. (B) Give a sheaf of modules on a topological space and a surjection of sheaves whose map on global sections is not surjective. Explain why this does not contradict the fact that the map is an epimorphism in `SheafOfModules R`.
5. (B) Show that the restriction `M.over X` of a locally free sheaf is locally free, by a refinement of the cover.
6. (C) Let $\varphi$ be a map of sheaves of rings on one site, with $F$ the identity functor. Show that `SheafOfModules.pullback φ` sends `unit S` to `unit R`, and deduce that the pullback of a quasicoherent sheaf is quasicoherent.

### Reference

<?reference?>
