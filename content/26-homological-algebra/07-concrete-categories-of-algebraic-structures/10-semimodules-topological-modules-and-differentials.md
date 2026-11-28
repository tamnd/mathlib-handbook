---
title: Semimodules, topological modules and differentials
kind: api
modules:
  - Mathlib.Algebra.Category.ModuleCat.Semi
  - Mathlib.Algebra.Category.ModuleCat.Topology.Basic
  - Mathlib.Algebra.Category.ModuleCat.Topology.Homology
  - Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
explains:
  E2: [SemimoduleCat, SemimoduleCat.isZero_iff_subsingleton, linearEquivIsoModuleIsoₛ, TopModuleCat, TopModuleCat.withModuleTopologyAdj, TopModuleCat.indiscreteAdj, TopModuleCat.freeAdj, TopModuleCat.instCategoryWithHomology, ModuleCat.Derivation, CommRingCat.KaehlerDifferential]
  E1: auto
families: []
requires: [V24.C05, V24.C08, V13, V14, V10]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Semimodules, topological modules and differentials

### Overview

This section treats three variants of the category of modules. The first is `SemimoduleCat R`, the category of modules over a semiring, in which negatives need not exist. It is the general frame, and `ModuleCat R` is equivalent to it when $R$ is a ring. The second is `TopModuleCat R`, the category of topological modules over a topological ring. It is not abelian, but it has all limits and colimits, kernels and cokernels with the right topologies, and a homology of short complexes. The third is the module of Kähler differentials of a map of commutative rings, as an object of `ModuleCat B`, with its universal derivation.

The three files are short. Each one applies the pattern of Section 1 (a bundled object, a wrapped morphism) to a new kind of structure, and adds the facts that the later volumes need. Chapter 9 uses the differentials to build the presheaf of differentials of a map of presheaves of rings.

### The library around it

#### Semimodules

Let $R$ be a semiring. An object of `SemimoduleCat R` is a type with `AddCommMonoid` and `Module R` instances, and a morphism is a linear map. The constructor is `SemimoduleCat.of R M`, the morphism of a linear map is `SemimoduleCat.ofHom f`, and the linear map of a morphism is `SemimoduleCat.Hom.hom`. The map `SemimoduleCat.Hom.hom` is a bijection, by `SemimoduleCat.hom_bijective`, and `SemimoduleCat.homLinearEquiv` makes it a linear equivalence when the morphisms form a module. The category is preadditive in the weak sense of semimodules: morphisms form a commutative monoid, `SemimoduleCat.instAddCommMonoidHom`, and composition is bilinear.

The basic facts are those of `ModuleCat` in Section 2:

| Lean name | Statement |
|---|---|
| `SemimoduleCat.isZero_iff_subsingleton` | $M$ is a zero object if and only if $M$ has at most one element |
| `linearEquivIsoModuleIsoₛ` | linear equivalences $X \simeq Y$ are the isomorphisms of objects |
| `CategoryTheory.Iso.toLinearEquivₛ` | an isomorphism gives a linear equivalence |
| `LinearEquiv.toModuleIsoₛ` | a linear equivalence gives an isomorphism |
| `SemimoduleCat.instHasZeroObject` | the zero module is a zero object |
| `SemimoduleCat.hasForgetToAddCommMonoid` | the forgetful functor to `AddCommMonCat` |

The functor `SemimoduleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier` says that the forgetful functor to types reflects isomorphisms. Proof: the inverse map of a bijective linear map is linear, because $f(f^{-1}(x) + f^{-1}(y)) = x + y$ and $f(r f^{-1}(x)) = r x$.

When $R$ is a ring, each module over $R$ in the sense of semirings has negatives: $-m = (-1) \cdot m$. So the equivalence `ModuleCat.equivalenceSemimoduleCat : ModuleCat R ≌ SemimoduleCat R` holds. The symmetric monoidal structure of Section 9 is first built on `SemimoduleCat`, with `SemimoduleCat.braiding`, and the instance `ModuleCat.MonoidalCategory.instBraidedSemimoduleCatFunctorEquivalenceSemimoduleCat` says that the equivalence respects the braidings. A typical semimodule that is not a module is $\mathbb{N}^n$ over $\mathbb{N}$, or a module over the tropical semiring.

#### Topological modules

Let $R$ be a topological ring. An object of `TopModuleCat R` is a module $M$ with a topology such that addition $M \times M \to M$ and scalar multiplication $R \times M \to M$ are continuous. A morphism is a continuous linear map, an element of `M →L[R] N`. The constructor is `TopModuleCat.of`, and a continuous linear equivalence gives an isomorphism, `TopModuleCat.ofIso`. The morphisms form an abelian group, so the category is preadditive, `TopModuleCat.instPreadditive`. The ring of endomorphisms of $M$ is the ring of continuous linear maps, by `TopModuleCat.endRingEquiv`.

The two forgetful functors go to `ModuleCat R` and to `TopCat`. Each one has adjoints:

| Lean name | Statement |
|---|---|
| `TopModuleCat.withModuleTopologyAdj` | the module topology is left adjoint to the forgetful functor to `ModuleCat R` |
| `TopModuleCat.indiscreteAdj` | the forgetful functor to `ModuleCat R` is left adjoint to the indiscrete topology |
| `TopModuleCat.freeAdj` | the free topological module is left adjoint to the forgetful functor to `TopCat` |

The module topology of $M$ is the finest topology that makes $M$ a topological module. A linear map out of $M$ with this topology is continuous for each target topology that makes the target a topological module, so `TopModuleCat.withModuleTopology` is left adjoint. The indiscrete topology has only $\varnothing$ and $M$ as open sets, so each map into it is continuous, which is the right adjoint property. The free topological module on a space $X$ is `TopModuleCat.freeObj X`: the module $R^{(X)}$ with the finest topology that makes it a topological module and makes $X \to R^{(X)}$, $x \mapsto e_x$, continuous.

#### Limits, colimits and homology of topological modules

The category `TopModuleCat R` has all limits and colimits, by `TopModuleCat.instHasLimits` and `TopModuleCat.instHasColimits`. The limit of a diagram is the limit $L$ in `ModuleCat R`, with the coarsest topology that makes the maps $L \to F(j)$ continuous: the cone `TopModuleCat.ofCone` uses the induced topology `TopModuleCat.induced`, and `TopModuleCat.isLimit` proves the universal property. The colimit is the colimit in `ModuleCat R` with the finest topology that makes it a topological module and makes the maps $F(j) \to C$ continuous: the cocone `TopModuleCat.ofCocone`, with `TopModuleCat.coinduced` and `TopModuleCat.isColimit`. The forgetful functor to `TopCat` preserves limits.

The category is not abelian. The identity map from $\mathbb{R}$ with its usual topology to $\mathbb{R}$ with the indiscrete topology is a monomorphism and an epimorphism, because it is bijective. It is not an isomorphism, because its inverse is not continuous. In an abelian category a map that is mono and epi is an isomorphism. Still, kernels and cokernels have a good form. The file `Mathlib.Algebra.Category.ModuleCat.Topology.Homology` defines `TopModuleCat.ker φ`, the kernel with the subspace topology, and `TopModuleCat.coker φ`, the quotient $N / \operatorname{range} \varphi$ with the quotient topology. The limit and colimit properties are `TopModuleCat.isLimitKer` and `TopModuleCat.isColimitCoker`. With these, the instance `TopModuleCat.instCategoryWithHomology` gives each short complex $M_1 \to M_2 \to M_3$ a homology object. Proof sketch: the left homology is a quotient of the kernel of $M_2 \to M_3$ and the right homology is a submodule of the cokernel of $M_1 \to M_2$. The comparison map between them is a bijection, because it is the comparison map in `ModuleCat R`. It is also a topological embedding, because the quotient maps of topological modules are open maps, so it is a homeomorphism. So the general homology of Chapter 1 applies in `TopModuleCat R`.

#### Derivations and Kähler differentials

Let $f \colon A \to B$ be a map of commutative rings and let $M$ be a $B$-module. The type `ModuleCat.Derivation M f` collects the $A$-derivations $d \colon B \to M$: the additive maps with
$$d(b b') = b \, d b' + b' \, d b, \qquad d(f(a)) = 0.$$
The constructor `ModuleCat.Derivation.mk` asks for exactly these three properties, and `ModuleCat.Derivation.d_mul` and `ModuleCat.Derivation.d_map` recover them. The point of the file is to state derivations with $f$ as a morphism of `CommRingCat`, with no `Algebra A B` instance in the context, because the presheaf version in Chapter 9 has a map of rings for each open set.

The module of differentials `CommRingCat.KaehlerDifferential f` is the object $\Omega_{B/A}$ of `ModuleCat B`, with the universal derivation `CommRingCat.KaehlerDifferential.D f` and its map `CommRingCat.KaehlerDifferential.d`. A derivation $D$ factors through it: `ModuleCat.Derivation.desc D` is the linear map $\Omega_{B/A} \to M$, and `ModuleCat.Derivation.desc_d` says that it sends $d b$ to $D b$. Two maps out of $\Omega_{B/A}$ agree when they agree on each $d b$, by `CommRingCat.KaehlerDifferential.ext`, because the elements $d b$ span $\Omega_{B/A}$. A commutative square of rings $A \to B$, $A' \to B'$ gives the map `CommRingCat.KaehlerDifferential.map` from $\Omega_{B/A}$ to $\Omega_{B'/A'}$, with $d b \mapsto d g'(b)$ by `CommRingCat.KaehlerDifferential.map_d`. The algebra of $\Omega_{B/A}$ itself is in Volume 10.

#### Common errors

1. A morphism of `TopModuleCat R` must be continuous. A linear map between topological modules is not a morphism until its continuity is proved, and `TopModuleCat.ofHom` takes a `ContinuousLinearMap`.
2. A map of `TopModuleCat R` that is mono and epi need not be an isomorphism. Do not look for a `CategoryTheory.Abelian` instance on this category.
3. `ModuleCat.Derivation M f` uses the algebra structure that $f$ induces. When `Algebra A B` is also present in the context, the two structures can differ by definitional unfolding, and lemmas about `Derivation` from Volume 10 may need a conversion.

### Exercises

1. (A) Show that the only morphism of `SemimoduleCat ℕ` from $\mathbb{N}$ to $\mathbb{N}$ that is an isomorphism is the identity.
2. (A) Show that $\mathbb{R}$ with the discrete topology is not a topological module over $\mathbb{R}$ with its usual topology.
3. (B) Compute the cokernel in `TopModuleCat ℝ` of the inclusion $\mathbb{Q} \to \mathbb{R}$, where $\mathbb{Q}$ has the subspace topology, and show that its topology is indiscrete.
4. (B) Compute $\Omega_{B/A}$ for $A = k$ and $B = k[x]$, and write the map `ModuleCat.Derivation.desc` for the derivation $d/dx \colon k[x] \to k[x]$.
5. (B) Prove that the indiscrete topology functor is right adjoint to the forgetful functor, as `TopModuleCat.indiscreteAdj` states.
6. (C) Show that the cokernel `TopModuleCat.coker φ` is Hausdorff if and only if the range of $\varphi$ is closed, and give a continuous linear map between Banach spaces whose range is not closed.

### Reference

<?reference?>
