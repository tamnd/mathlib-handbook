---
title: The sheaf of smooth functions
kind: api
modules: [Mathlib.Geometry.Manifold.Sheaf.Basic, Mathlib.Geometry.Manifold.Sheaf.Smooth, Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace]
explains:
  E2: [StructureGroupoid.LocalInvariantProp.sheaf, smoothSheaf, smoothSheaf.eval_surjective, smoothSheafCommRing, smoothSheafCommRing.isUnit_stalk_iff, ChartedSpace.locallyRingedSpace, ChartedSpace.locallyRingedSpaceMap]
  E1: auto
families: []
requires: [V23.C01, V23.C02, V28.C01, V28.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The sheaf of smooth functions

### Overview

Let $M$ be a manifold. For each open set $U \subseteq M$, let $\mathcal{O}(U)$ be the set of smooth functions $U \to \mathbb{K}$. Restriction of functions makes $\mathcal{O}$ a presheaf, and smoothness is a local property, so $\mathcal{O}$ is a sheaf. Pointwise addition and multiplication make it a sheaf of commutative rings. At each point $x$, a germ of a smooth function is invertible exactly when its value at $x$ is not zero. So the stalk at $x$ is a local ring, and its maximal ideal is the set of germs that vanish at $x$. This makes $(M, \mathcal{O})$ a locally ringed space, the same kind of object as a scheme.

Mathlib builds this structure in three modules. The module `Mathlib.Geometry.Manifold.Sheaf.Basic` turns any local invariant property of Chapter 1 into a sheaf of types. The module `Mathlib.Geometry.Manifold.Sheaf.Smooth` applies this to smoothness and adds the algebraic structure. The module `Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace` proves that the stalks are local rings and makes a manifold an object of the category of locally ringed spaces of Volume 28. In this section, "smooth" means $C^\infty$, written `∞` in the library.

### The library around it

#### Sheaves from local invariant properties

Let $G$ and $G'$ be structure groupoids on the model spaces $H$ and $H'$, and let $P$ be a property of maps $H \to H'$ that is a local invariant property for $G$ and $G'$. Chapter 1 lifts $P$ to the predicate `ChartedSpace.LiftProp` on maps between charted spaces $M$ and $M'$. The work of the module `Mathlib.Geometry.Manifold.Sheaf.Basic` is to show that this predicate is local in the sense of sheaf theory.

1. `StructureGroupoid.LocalInvariantProp.localPredicate` is the `TopCat.LocalPredicate` on functions from open subsets of $M$ to $M'$ that holds when the function satisfies `ChartedSpace.LiftProp P`. Its two fields are the two facts to prove: the property passes to smaller open sets, and a function that has the property near each point has it on its whole domain.
2. `StructureGroupoid.LocalInvariantProp.sheaf` is the sheaf of types `TopCat.subsheafToTypes` of this predicate. Its sections over $U$ are the functions $U \to M'$ that satisfy the lifted property.
3. `StructureGroupoid.LocalInvariantProp.section_spec` says that each section satisfies `ChartedSpace.LiftProp P`, and the instance `StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun` lets a section be applied to points.

The sheaf lives on the object `TopCat.of M` of the category of topological spaces. The instances `TopCat.of.chartedSpace` and `TopCat.of.hasGroupoid` copy the charts and the groupoid of $M$ to this object, so that the lemmas of Chapter 1 apply to it.

#### The sheaf of smooth maps

Let `IM` be a model with corners for $M$ and `I` a model with corners for a second manifold $N$. The sheaf `smoothSheaf IM I M N` is the sheaf of the preceding part for the local invariant property of $C^\infty$ maps of Section 1. Its value on an open set $U$ is, by definition, the type `ContMDiffMap` of smooth maps from $U$ to $N$. The lemma `smoothSheaf.obj_eq` states this equality, and it holds by `rfl`. The lemma `smoothSheaf.contMDiff_section` gives the smoothness of a section as a `ContMDiff` statement.

The stalk at $x$ is `TopCat.Presheaf.stalk` of the presheaf, and the germ of a section is `TopCat.Presheaf.germ`. The library evaluates germs at the point.

| Lean name | Statement |
|---|---|
| `smoothSheaf.eval` | the map from the stalk at $x$ to $N$ that evaluates a germ at $x$ |
| `smoothSheaf.evalAt` | evaluation at $x$ on the sections over one open neighbourhood of $x$ |
| `smoothSheaf.evalHom` | `smoothSheaf.eval` as a morphism in the category of types |
| `smoothSheaf.eval_germ` | the germ of $f$ evaluates to $f(x)$ |
| `smoothSheaf.eval_surjective` | each point of $N$ is the value of some germ |

The proof of `smoothSheaf.eval_surjective` uses the constant maps, which are smooth on all of $M$. If $N$ has two distinct points, the stalk is therefore nontrivial, and the instance `instNontrivialStalkPresheafSmoothSheaf` records this.

A smooth map $f : M \to P$ pulls smooth maps back: a smooth map $g$ on an open set $V \subseteq P$ gives the smooth map $g \circ f$ on $f^{-1}(V)$. The morphism `ContMDiff.smoothSheafHom` packages this as a morphism of sheaves from the sheaf on $P$ to the pushforward `TopCat.Sheaf.pushforward` of the sheaf on $M$.

#### Algebraic structure

When the target has algebraic operations that are smooth, the sections inherit them pointwise. The library has one sheaf for each structure.

1. `smoothSheafGroup` and `smoothSheafCommGroup`, for a target that is a Lie group (`LieGroup`), with values in `GrpCat` and `CommGrpCat`.
2. `smoothSheafRing` and `smoothSheafCommRing`, for a target ring with smooth operations (`ContMDiffRing`), with values in `RingCat` and `CommRingCat`.
3. The additive forms `smoothSheafAddGroup` and `smoothSheafAddCommGroup`, which `to_additive` generates.

Each sheaf has a presheaf form, such as `smoothPresheafGroup` and `smoothPresheafCommRing`, and the sheaf is that presheaf with the sheaf property of `smoothSheaf`. A smooth homomorphism $\varphi : A \to A'$ of commutative Lie groups gives the morphism `smoothSheafCommGroup.compLeft` that composes each section with $\varphi$, and `smoothSheafAddCommGroup.compLeft` is the additive form.

For the sheaf of commutative rings, `smoothSheafCommRing.forgetStalk` identifies its stalk with the stalk of the sheaf of types. Evaluation becomes a ring homomorphism `smoothSheafCommRing.eval` from the stalk to $R$, with the variants `smoothSheafCommRing.evalAt` and `smoothSheafCommRing.evalHom` and the lemmas `smoothSheafCommRing.eval_germ`, `smoothSheafCommRing.evalHom_germ` and `smoothSheafCommRing.eval_surjective`. Pullback by a smooth map is a morphism of sheaves of rings, `ContMDiff.smoothSheafCommRingHom`.

#### Manifolds as locally ringed spaces

The structure sheaf of $M$ is `smoothSheafCommRing IM 𝓘(𝕜) M 𝕜`, where `𝓘(𝕜)` is the model `modelWithCornersSelf` of the field $\mathbb{K}$ over itself. The main theorem of the module `Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace` is `smoothSheafCommRing.isUnit_stalk_iff`: a germ $f$ at $x$ is a unit exactly when it is not in the kernel of `smoothSheafCommRing.eval`, that is, when its value at $x$ is not zero.

One direction holds in every ring: a ring homomorphism sends units to units, and the units of $\mathbb{K}$ are the nonzero elements. For the other direction, represent the germ by a smooth function $f$ on an open neighbourhood $U$ of $x$ with $f(x) \neq 0$. The set $V \subseteq U$ where $f$ is not zero is open and contains $x$, and $1/f$ is smooth on $V$. The germ of $1/f$ is the inverse of the germ of $f$.

The consequences follow in order.

1. `smoothSheafCommRing.nonunits_stalk` says that the nonunits of the stalk form the kernel of evaluation.
2. The instance `smoothSheafCommRing.instLocalRing_stalk` gives `IsLocalRing` for the stalk, because a sum of two germs that vanish at $x$ vanishes at $x$.
3. `ChartedSpace.locallyRingedSpace` is $M$ as an object of `AlgebraicGeometry.LocallyRingedSpace`, with the structure sheaf.
4. `ChartedSpace.locallyRingedSpaceMap` is the morphism of locally ringed spaces that a smooth map $f : M \to N$ gives. Its map of spaces is $f$ (the simp lemma `ChartedSpace.locallyRingedSpaceMap_base`), and its map of sheaves is `ContMDiff.smoothSheafCommRingHom`. The lemma `ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom` says that the map on stalks commutes with evaluation.
5. `ChartedSpace.locallyRingedSpace_id` and `ChartedSpace.locallyRingedSpace_comp` say that the construction respects identities and composition.
6. For an open set $U$ of $M$, the inclusion of $U$ is an open immersion in the sense of `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`, and `ChartedSpace.restrictLocallyRingedSpaceIso` identifies the locally ringed space of the manifold $U$ with the restriction of the locally ringed space of $M$ to $U$.

The library does not prove the converse of item 4, that each morphism of locally ringed spaces between two manifolds comes from a smooth map. The source file lists it as future work.

#### Common errors

1. Using a manifold $M$ and a target $N$ in different universes. The construction needs `M` and `N` in the same universe `u`, because the sheaves take values in `Type u` and in categories such as `CommRingCat`. A real manifold on a type in `Type 1` has no structure sheaf with values in $\mathbb{R}$.
2. Treating a germ as a function. An element of the stalk is an equivalence class of sections. To get a value, apply `smoothSheaf.eval` or `smoothSheafCommRing.eval`, and to compute it on a representative, rewrite with `smoothSheaf.eval_germ`.
3. Expecting the sheaf of $C^n$ functions for a finite $n$. The sheaves of these modules use $C^\infty$ only. For another class, apply `StructureGroupoid.LocalInvariantProp.sheaf` directly to the local invariant property of that class.

### Exercises

1. (A) Use `smoothSheaf.obj_eq` and `smoothSheaf.contMDiff_section` to show that a section of `smoothSheaf IM I M N` over $U$ is continuous.
2. (A) Show that the constant germ with value $1$ is not in the kernel of `smoothSheafCommRing.eval`, and deduce from `smoothSheafCommRing.isUnit_stalk_iff` that it is a unit.
3. (B) Let $M = \mathbb{R}$ and $x = 0$. Prove that the germ of the identity function generates the maximal ideal of the stalk at $0$. Hint: for a smooth $f$ with $f(0) = 0$, write $f(t) = t \int_0^1 f'(st)\,ds$.
4. (B) Prove that the stalk of the structure sheaf of $\mathbb{R}$ at $0$ is not a noetherian ring, using the function that is $e^{-1/t^2}$ for $t \neq 0$ and $0$ at $0$.
5. (C) Let $f : M \to N$ be a smooth map. Use `ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom` to show that the map on stalks sends the germs that vanish at $f(x)$ to germs that vanish at $x$, and explain why this is the condition on a morphism of locally ringed spaces.

### Reference

<?reference?>
