---
title: Finitely generated modules and the monoidal structure
kind: api
modules:
  - Mathlib.Algebra.Category.FGModuleCat.Basic
  - Mathlib.Algebra.Category.FGModuleCat.Abelian
  - Mathlib.Algebra.Category.FGModuleCat.Colimits
  - Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
  - Mathlib.Algebra.Category.FGModuleCat.Limits
  - Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
  - Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
  - Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
  - Mathlib.Algebra.Category.ModuleCat.ExteriorPower
  - Mathlib.Algebra.Category.ModuleCat.Tannaka
explains:
  E2: [FGModuleCat, ModuleCat.isFG, FGModuleCat.instAbelian, FGModuleCat.rightRigidCategory, instEssentiallySmallFGModuleCat, ModuleCat.instMonoidalClosed, ModuleCat.MonoidalCategory.symmetricCategory, ModuleCat.instMonoidalExtendScalars, ModuleCat.exteriorPower.functor, ringEquivEndForget₂]
  E1: auto
families: []
requires: [V24.C07, V24.C08, V07, V08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finitely generated modules and the monoidal structure

### Overview

Section 2 gives the tensor product of modules over a commutative ring as a monoidal structure on `ModuleCat R`. This section completes that structure. The tensor product is symmetric, the module of linear maps is an internal Hom, extension of scalars is a monoidal functor, and the exterior powers are functors. The section also treats the full subcategory `FGModuleCat R` of finitely generated modules. Over a Noetherian ring it is abelian, and over a field it is the rigid category of finite dimensional vector spaces, in which each object has a dual.

The last file proves a small Tannaka duality: a ring $R$ is recovered from its module category as the ring of endomorphisms of the forgetful functor to abelian groups. Representation theory and the theory of fusion categories use the same idea in a larger form.

### The library around it

#### The symmetric monoidal closed structure

Let $R$ be a commutative ring. The file `Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric` gives the braiding $M \otimes N \to N \otimes M$, $m \otimes n \mapsto n \otimes m$, with `ModuleCat.MonoidalCategory.braiding_hom_apply`. The instance `ModuleCat.MonoidalCategory.symmetricCategory` says that the braiding squares to the identity, so `ModuleCat R` is symmetric monoidal. The hexagon axioms hold because both sides send $m \otimes n \otimes p$ to the same pure tensor, and pure tensors generate. The file has the same results for `SemimoduleCat`, the category of modules over a commutative semiring, described in Section 10.

The file `Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed` gives the internal Hom. The instance `ModuleCat.instMonoidalClosed` makes $\operatorname{Hom}_R(M, -)$ right adjoint to $M \otimes -$. The bijection is `ModuleCat.monoidalClosedHomEquiv`:
$$\operatorname{Hom}(M \otimes N, P) \cong \operatorname{Hom}(N, \operatorname{Hom}_R(M, P)),$$
the currying of bilinear maps, with `ModuleCat.monoidalClosed_curry` and `ModuleCat.monoidalClosed_uncurry` as its formulas. The evaluation is `ModuleCat.ihom_ev_app` and the coevaluation is `ModuleCat.ihom_coev_app`.

#### Change of rings and the tensor product

Let $f \colon R \to S$ be a map of commutative rings. The file `Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction` proves that extension of scalars $M \mapsto S \otimes_R M$ is a monoidal functor, by `ModuleCat.instMonoidalExtendScalars`. The structure map is the isomorphism
$$(S \otimes_R M) \otimes_S (S \otimes_R N) \cong S \otimes_R (M \otimes_R N),$$
with `ModuleCat.extendScalars_μ` and `ModuleCat.extendScalars_δ`. Restriction of scalars is only lax monoidal, by `ModuleCat.instLaxMonoidalRestrictScalars`: for two $S$-modules $M$ and $N$, the map $M \otimes_R N \to M \otimes_S N$ exists, but it is not an isomorphism in general. For example, with $R = \mathbb{Z}$ and $S = \mathbb{Q}$, the map $\mathbb{Q} \otimes_{\mathbb{Z}} \mathbb{Q} \to \mathbb{Q} \otimes_{\mathbb{Q}} \mathbb{Q}$ is an isomorphism, but for $S = \mathbb{Z}[x]$ the map $S \otimes_{\mathbb{Z}} S \to S \otimes_S S = S$ is not injective. The lax structure is the one that the adjunction of Section 2 induces from the monoidal left adjoint.

#### Exterior powers

The file `Mathlib.Algebra.Category.ModuleCat.ExteriorPower` makes the exterior power a functor of `ModuleCat R`. The object `ModuleCat.exteriorPower M n` is $\Lambda^n M$, the module of the universal alternating map $M^n \to \Lambda^n M$. The type `ModuleCat.AlternatingMap M N n` collects the alternating maps, and `ModuleCat.exteriorPower.desc` turns an alternating map into a morphism out of $\Lambda^n M$. The extensionality lemma `ModuleCat.exteriorPower.hom_ext` says that two morphisms out of $\Lambda^n M$ agree when they agree on the elements $m_1 \wedge \dots \wedge m_n$, given by `ModuleCat.exteriorPower.mk`. The functor `ModuleCat.exteriorPower.functor R n` sends $f \colon M \to N$ to $\Lambda^n f$, with `ModuleCat.exteriorPower.map_mk`:
$$\Lambda^n f(m_1 \wedge \dots \wedge m_n) = f(m_1) \wedge \dots \wedge f(m_n).$$
In low degree, `ModuleCat.exteriorPower.iso₀` gives $\Lambda^0 M \cong R$ and `ModuleCat.exteriorPower.iso₁` gives $\Lambda^1 M \cong M$, natural in $M$ by `ModuleCat.exteriorPower.natIso₀` and `ModuleCat.exteriorPower.natIso₁`. The algebra of exterior powers is in Volume 8.

#### The category of finitely generated modules

The file `Mathlib.Algebra.Category.FGModuleCat.Basic` defines the property `ModuleCat.isFG R` of a module to be finitely generated, with `ModuleCat.isFG_iff`, and `FGModuleCat R` as the full subcategory of `ModuleCat R` that it defines. The constructor is `FGModuleCat.of`, and a linear equivalence gives an isomorphism by `LinearEquiv.toFGModuleCatIso`. The carrier of an object is a finite module by the instance `FGModuleCat.instFiniteCarrier`. When $R$ is commutative, the tensor product of two finitely generated modules is finitely generated, so the subcategory is monoidal, `FGModuleCat.instIsMonoidalModuleCatIsFG`.

The finite limits and colimits of `FGModuleCat R` are those of `ModuleCat R`:

| Lean name | Statement |
|---|---|
| `FGModuleCat.forget₂CreatesColimit` | the inclusion creates finite colimits |
| `FGModuleCat.instHasFiniteColimits` | `FGModuleCat R` has finite colimits |
| `FGModuleCat.forget₂CreatesLimit` | the inclusion creates finite limits, for $R$ Noetherian |
| `FGModuleCat.instHasFiniteLimits` | `FGModuleCat R` has finite limits, for $R$ Noetherian |
| `FGModuleCat.instAbelian` | `FGModuleCat R` is abelian, for $R$ Noetherian |

Colimits need no hypothesis on $R$: a finite colimit is a quotient of a finite direct sum of finitely generated modules, so it is finitely generated. Limits need the Noetherian hypothesis, because a finite limit is a submodule of a finite product, and a submodule of a finitely generated module is finitely generated only over a Noetherian ring. For example, over the ring $R = k[x_1, x_2, \dots]$ the kernel of $R \to k$ is not finitely generated. With kernels and cokernels in hand, `FGModuleCat.instAbelian` follows from the abelian structure of `ModuleCat R`, because the comparison map from the coimage to the image is the same map in both categories.

The file `Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall` proves `instEssentiallySmallFGModuleCat`: up to isomorphism, the finitely generated modules form a set. Proof: each such module is a quotient $R^n / S$, and the structure `FGModuleRepr R` records the pair $(n, S)$. These pairs form a type in the universe of $R$, and the functor `FGModuleRepr.embed` is an equivalence onto `FGModuleCat R`.

#### Finite dimensional vector spaces as a rigid category

Let $K$ be a field. Then `FGModuleCat K` is the category of finite dimensional vector spaces. The dual of $V$ is `FGModuleCat.FGModuleCatDual K V`, the space $V^* = \operatorname{Hom}_K(V, K)$. The evaluation `FGModuleCat.FGModuleCatEvaluation` is $V^* \otimes V \to K$, $\varphi \otimes v \mapsto \varphi(v)$, and the coevaluation `FGModuleCat.FGModuleCatCoevaluation` is $K \to V \otimes V^*$, $1 \mapsto \sum_i e_i \otimes e_i^*$ for a basis $(e_i)$. The triangle identities say that
$$v \mapsto \sum_i e_i \, e_i^*(v) = v,$$
which is the expansion of a vector in a basis. So $V^*$ is a right dual of $V$, by `FGModuleCat.exactPairing`, and `FGModuleCat.rightRigidCategory` makes the category right rigid. The coevaluation needs a finite basis, so this structure does not extend to all of `ModuleCat K`. The internal Hom of `ModuleCat K` restricts to finite dimensional spaces, `FGModuleCat.instIsMonoidalClosedModuleCatIsFG`.

#### Tannaka duality for rings

The file `Mathlib.Algebra.Category.ModuleCat.Tannaka` proves `ringEquivEndForget₂`: the ring $R$ is isomorphic to the ring of natural endomorphisms of the additive forgetful functor $U \colon \mathrm{Mod}_R \to \mathbf{Ab}$. Proof: an element $r \in R$ gives the natural transformation with components $m \mapsto r m$. Conversely, a natural transformation $\eta$ is determined by $r = \eta_R(1)$. For $m \in M$, the map $R \to M$, $s \mapsto s m$, is linear, so naturality gives $\eta_M(m) = \eta_M(1 \cdot m) = \eta_R(1) m = r m$. The two maps are inverse ring maps.

#### Common errors

1. `FGModuleCat.instAbelian` and the finite limits need `IsNoetherianRing R`. Over a ring that is not Noetherian, `FGModuleCat R` has cokernels but not kernels.
2. Restriction of scalars is lax monoidal, not monoidal. A proof that uses its structure map as an isomorphism fails, except in special cases such as localizations.
3. The rigid structure of `FGModuleCat K` needs a field $K$. Over a general commutative ring, the finitely generated projective modules have duals, but `FGModuleCat R` does not have this instance.

### Exercises

1. (A) Show that $\Lambda^n K^m = 0$ for $n > m$, with `ModuleCat.exteriorPower.hom_ext`, and compute $\Lambda^2 K^2$.
2. (A) Write the braiding of $K^2 \otimes K^2$ as a $4 \times 4$ matrix in the basis $e_i \otimes e_j$.
3. (B) Prove the triangle identity $(\mathrm{id}_V \otimes \mathrm{ev}) \circ (\mathrm{coev} \otimes \mathrm{id}_V) = \mathrm{id}_V$ for $V = K^n$, as in `FGModuleCat.exactPairing`.
4. (B) Show that `FGModuleCat ℤ` is abelian, and give a monomorphism in it that is not split.
5. (B) Compute the image of $r \in R$ under `ringEquivEndForget₂` for $R = \mathbb{Z}/6$, and check naturality on the map $\mathbb{Z}/6 \to \mathbb{Z}/3$.
6. (C) Prove that a finite limit of finitely generated modules over a Noetherian ring is finitely generated, the key step of `FGModuleCat.forget₂CreatesLimit`.

### Reference

<?reference?>
