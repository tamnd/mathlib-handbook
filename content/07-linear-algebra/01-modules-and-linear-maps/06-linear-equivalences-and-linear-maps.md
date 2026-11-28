---
title: Constructions of linear equivalences and linear maps
kind: api
modules:
  - Mathlib.Algebra.Module.Equiv.Basic
  - Mathlib.Algebra.Module.LinearMap.Basic
  - Mathlib.Algebra.Module.LinearMap.DivisionRing
  - Mathlib.Algebra.Module.LinearMap.Prod
  - Mathlib.Algebra.Module.LinearMap.Rat
  - Mathlib.Algebra.Module.LinearMap.Star
  - Mathlib.LinearAlgebra.LeftExact
explains:
  E2: [LinearEquiv.ofLinearMap, LinearEquiv.conj, LinearEquiv.arrowCongr, Module.End.isUnit_iff, AddEquiv.toIntLinearEquiv, LinearEquiv.smulOfNeZero, LinearMap.funLeft, LinearMap.surjective_iff_ne_zero, AddMonoidHom.toRatLinearMap, LinearMap.exact_lcomp_of_exact_of_surjective]
  E1: auto
families: []
requires: [V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Constructions of linear equivalences and linear maps

### Overview

Section 2 defined linear equivalences and gave `LinearEquiv.refl`, `LinearEquiv.symm` and `LinearEquiv.trans`. This section is the toolbox for making new linear equivalences and linear maps from old ones. It covers equivalences from a pair of inverse linear maps, the group of automorphisms of a module, conjugation of endomorphisms by an equivalence, the change of domain and codomain in a space of linear maps, and the transfer of additive equivalences to $\mathbb{Z}$-linear and $\mathbb{Q}$-linear ones. It also gives some small facts that are often needed: a linear map over a ring with a unit is linear over $\mathbb{Q}$ when it is additive, and a nonzero linear form on a vector space is surjective.

### The library around it

#### Equivalences from inverse maps

The most direct way to build a linear equivalence is to give a linear map $f : M \to M_2$, a linear map $g : M_2 \to M$, and proofs that $f \circ g = \operatorname{id}$ and $g \circ f = \operatorname{id}$. This is `LinearEquiv.ofLinearMap f g h₁ h₂`, with `LinearEquiv.coe_ofLinearMap` and `LinearEquiv.symm_ofLinearMap` as its rewriting lemmas. The two hypotheses are equalities of linear maps, so a proof usually starts with `LinearMap.ext` and then computes on one element. The form `LinearEquiv.ofLinearMap` takes the same data.

Other sources of equivalences are an additive equivalence that commutes with the action, `AddEquiv.toLinearEquiv`, and an equivalence of types whose forward map is linear, `Equiv.toLinearEquiv`. For a bijective linear map, `LinearEquiv.ofBijective` of Section 5 is the better tool, since it needs no inverse.

#### The automorphism group

The linear automorphisms of $M$ form a group under composition, by the instance `LinearEquiv.automorphismGroup`. The product is composition, $(f g)(x) = f(g(x))$, by the general lemma `mul_apply_eq_comp` for the class `IsMulApplyEqComp`, so `LinearEquiv.mul_eq_trans` says that `f * g = g.trans f`. The order is reversed: `trans` applies its first argument first. The powers are iterates, `FunLike.coe_pow_eq_iterate`. The map `LinearEquiv.automorphismGroup.toLinearMapMonoidHom` sends an automorphism to its endomorphism.

**Theorem.** An endomorphism $f$ of $M$ is a unit of $\operatorname{End}_R(M)$ if and only if it is bijective.

*Proof.* If $f g = g f = 1$, then $g$ is a two sided inverse of $f$ as a function, so $f$ is bijective. If $f$ is bijective, its inverse function is linear by Section 2, and it is an inverse in $\operatorname{End}_R(M)$. $\square$

This is `Module.End.isUnit_iff`. The group of units of $\operatorname{End}_R(M)$ is the general linear group `LinearMap.GeneralLinearGroup R M`, and `LinearMap.GeneralLinearGroup.generalLinearEquiv` identifies it with the automorphism group.

The automorphism group acts on $M$ by the instance `LinearEquiv.applyDistribMulAction`, with `LinearEquiv.smul_def : f • a = f a`. An action of a group $S$ on $M$ by linear maps gives a homomorphism into the automorphisms, `DistribMulAction.toModuleAut`. The special cases are the multiplication by a unit, `LinearEquiv.smulOfUnit`, and, over a field, the multiplication by a nonzero scalar, `LinearEquiv.smulOfNeZero K M a ha`. In a ring $A$, the left and right multiplications by a unit are equivalences: `Units.mulLeftLinearEquiv` and `Units.mulRightLinearEquiv`. The negation is the equivalence `LinearEquiv.neg R`.

#### Conjugation and change of domain

Let $e : M_1 \simeq M_2$ be a linear equivalence. An endomorphism $f$ of $M_1$ gives the endomorphism $e f e^{-1}$ of $M_2$.

**Theorem.** Conjugation by $e$ is a ring isomorphism $\operatorname{End}(M_1) \simeq \operatorname{End}(M_2)$.

*Proof.* The map $f \mapsto e f e^{-1}$ has the inverse $g \mapsto e^{-1} g e$. It respects sums since composition is bilinear. It respects products since $e f e^{-1} e g e^{-1} = e f g e^{-1}$, and it sends $1$ to $e e^{-1} = 1$. $\square$

As a linear equivalence this is `LinearEquiv.conj e`, and as a ring isomorphism it is `LinearEquiv.conjRingEquiv e`. The value is `LinearEquiv.conj_apply_apply : (e.conj f) x = e (f (e.symm x))`. The rules `LinearEquiv.conj_comp`, `LinearEquiv.conj_id`, `LinearEquiv.conj_trans` and `LinearEquiv.conj_symm_conj` follow. Conjugation keeps the trace, the determinant and the eigenvalues, and Chapter 4 and Chapter 5 use it to move from an abstract endomorphism to a matrix.

The general form changes both the domain and the codomain. For $e_1 : M_1 \simeq M_1'$ and $e_2 : M_2 \simeq M_2'$, the map `LinearEquiv.arrowCongr e₁ e₂` sends $f : M_1 \to M_2$ to $e_2 f e_1^{-1}$. It is a linear equivalence between the two spaces of linear maps, with `LinearEquiv.arrowCongr_apply`. The one sided forms are `LinearEquiv.congrRight` and `LinearEquiv.congrLeft`. For function spaces, a map $f : m \to n$ of index types gives the linear map `LinearMap.funLeft R M f : (n → M) →ₗ[R] (m → M)`, $g \mapsto g \circ f$. It is injective when $f$ is surjective (`LinearMap.funLeft_injective_of_surjective`), and surjective when $f$ is injective. An equivalence of index types gives the equivalence `LinearEquiv.funCongrLeft`.

Some other equivalences of this file:

| Lean name | Equivalence |
|---|---|
| `LinearEquiv.curry` | functions on $V \times V_2$ and curried functions |
| `LinearEquiv.piUnique` | functions on a type with one element and their value |
| `LinearEquiv.sumPiEquivProdPi` | functions on $S \oplus T$ and pairs of functions |
| `LinearEquiv.ofSubsingleton` | two modules with at most one element |
| `LinearMap.ringLmapEquivSelf` | $R$-linear maps $R \to M$ and elements of $M$ |
| `LinearEquiv.restrictScalars` | an equivalence over $R$ seen over a smaller ring $S$ |

The equivalence `LinearMap.ringLmapEquivSelf` sends $f$ to $f(1)$. Its inverse sends $x$ to $r \mapsto r x$, which is `LinearMap.smulRight 1 x`.

#### Additive maps over the integers and the rationals

Every additive group is a $\mathbb{Z}$-module in one way, by Section 4. So an additive map is $\mathbb{Z}$-linear, and an additive equivalence is a $\mathbb{Z}$-linear equivalence. This is `AddEquiv.toIntLinearEquiv`, with `AddEquiv.coe_toIntLinearEquiv` to say that the function is the same. The space of additive maps is the space of $\mathbb{Z}$-linear maps: `addMonoidHomLequivInt` is this equivalence, and `addMonoidEndRingEquivInt` is the ring isomorphism between the additive endomorphisms and the $\mathbb{Z}$-linear endomorphisms. The versions over $\mathbb{N}$ are `AddEquiv.toNatLinearEquiv` and `addMonoidHomLequivNat`.

**Theorem.** Let $M$ and $M_2$ be $\mathbb{Q}$-vector spaces. Each additive map $f : M \to M_2$ is $\mathbb{Q}$-linear.

*Proof.* The map $f$ is $\mathbb{Z}$-linear. For $n \ne 0$ and $x \in M$, $n f(x / n) = f(x)$, so $f(x / n) = f(x) / n$. For $q = m / n$ this gives $f(q x) = m f(x / n) = q f(x)$. $\square$

This is `AddMonoidHom.toRatLinearMap`, in `Mathlib.Algebra.Module.LinearMap.Rat`. The map is injective (`AddMonoidHom.toRatLinearMap_injective`) and keeps the function (`AddMonoidHom.coe_toRatLinearMap`). The same argument is `map_rat_smul` of Section 4.

#### Small facts about linear maps

The file `Mathlib.Algebra.Module.LinearMap.Basic` gives the left and right multiplication maps of an algebra, `LinearMap.mulLeft R a` and `LinearMap.mulRight R a`. They are injective in $a$ (`LinearMap.mulLeft_inj`), and they turn products into compositions, `LinearMap.mulLeft_mul` and `LinearMap.mulRight_mul`. The order is reversed for the right multiplication. The space of semilinear maps into a torsion free module is torsion free, by the instance `LinearMap.instIsTorsionFree`. The same file lets the domain action act on linear maps: `DomMulAct.mk_smul_linearMap_apply` states $(a \cdot f)(x) = f(a \cdot x)$.

**Theorem.** A linear form $f : M \to K$ on a vector space over a division ring is surjective if and only if $f \ne 0$.

*Proof.* If $f \ne 0$, pick $x$ with $f(x) \ne 0$. For $c \in K$, the vector $c f(x)^{-1} x$ has the value $c$. $\square$

This is `LinearMap.surjective_iff_ne_zero` in `Mathlib.Algebra.Module.LinearMap.DivisionRing`, with the one way form `LinearMap.surjective`. The consequence `LinearMap.range_smulRight_apply` says that the range of $v \mapsto f(v) x$ is the line through $x$ for $f \ne 0$.

The file `Mathlib.Algebra.Module.LinearMap.Prod` proves that addition and subtraction $M \times M \to M$ are linear maps in the sense of `IsLinearMap`: `IsLinearMap.isLinearMap_add` and `IsLinearMap.isLinearMap_sub`. The file `Mathlib.Algebra.Module.LinearMap.Star` gives the notation `M →ₗ⋆[R] M₂` for the conjugate linear maps, the semilinear maps over `starRingEnd R`, and `M ≃ₗ⋆[R] M₂` for the conjugate linear equivalences. On $\mathbb{C}$, these are the maps with $f(c x) = \bar{c} f(x)$, which appear in the theory of inner products.

Composition on the right with a fixed linear map $g : M_2 \to M_3$ is the linear map `LinearMap.lcomp R N g` from $M_3 \to N$ to $M_2 \to N$, over a commutative ring. It is injective when $g$ is surjective (`LinearMap.lcomp_injective_of_surjective`).

**Theorem (`LinearMap.exact_lcomp_of_exact_of_surjective`).** Let $M_1 \xrightarrow{f} M_2 \xrightarrow{g} M_3 \to 0$ be exact, and let $N$ be a module. Then the sequence $(M_3 \to N) \to (M_2 \to N) \to (M_1 \to N)$ of the compositions with $g$ and with $f$ is exact.

*Proof.* The composite $h \circ g \circ f$ is $0$ because $g \circ f = 0$. Conversely, let $h : M_2 \to N$ with $h \circ f = 0$. Then $h$ vanishes on the range of $f$, which is the kernel of $g$, so it passes to the quotient $M_2 / \ker g$. This quotient is isomorphic to $M_3$ because $g$ is surjective, and the result is a map $k : M_3 \to N$ with $k \circ g = h$. $\square$

With the injectivity, this says that the functor of linear maps into $N$ is left exact. Exact sequences are in Volume 26.

#### Common errors

1. Reading `f * g` in the automorphism group as `f.trans g`. The product applies $g$ first, so `f * g = g.trans f`.
2. Proving the hypotheses of `LinearEquiv.ofLinearMap` by `rfl` when the maps are not inverse by definition. The hypotheses are equalities of linear maps; use `LinearMap.ext` and compute on one vector.
3. Using `LinearEquiv.smulOfNeZero` over a ring that is not a field. Over a general ring, the scalar must be a unit, and the correct tool is `LinearEquiv.smulOfUnit`.

### Exercises

1. (A) Build the linear equivalence $\mathbb{Q}^2 \to \mathbb{Q}^2$, $(x, y) \mapsto (x + y, y)$, with `LinearEquiv.ofLinearMap`, and give its inverse.
2. (A) Show that `LinearEquiv.conj e` sends the identity to the identity and a projection to a projection.
3. (B) Let $f : m \to n$ be a map of finite types. Show that `LinearMap.funLeft R M f` is injective if and only if $f$ is surjective, when $M \ne 0$.
4. (B) Show that an additive map $\mathbb{R} \to \mathbb{R}$ is $\mathbb{Q}$-linear. Give an argument that it need not be $\mathbb{R}$-linear, with a basis of $\mathbb{R}$ over $\mathbb{Q}$.
5. (B) Let $f$ and $g$ be nonzero linear forms on a vector space with the same kernel. Show that $g = c f$ for some $c \ne 0$.
6. (C) Show that the center of the ring $\operatorname{End}_K(V)$ of a vector space $V$ over a field $K$ is the set of the maps $x \mapsto c x$. Hint: an endomorphism in the center commutes with each projection onto a line.

### Reference

<?reference?>
