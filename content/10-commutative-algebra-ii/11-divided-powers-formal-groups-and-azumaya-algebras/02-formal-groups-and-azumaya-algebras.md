---
title: Formal groups and Azumaya algebras
kind: api
modules:
  - Mathlib.RingTheory.FormalGroup.Basic
  - Mathlib.Algebra.Azumaya.Defs
  - Mathlib.Algebra.Azumaya.Basic
  - Mathlib.Algebra.Azumaya.Matrix
explains:
  E2: [FormalGroup, FormalGroup.Xzero_eq_X, FormalGroup.𝔾ₘ, FormalGroup.Point, IsAzumaya, IsAzumaya.matrix, IsAzumaya.id, Algebra.IsCentral.instIsAzumaya]
  E1: auto
families: []
requires: [V08, V09, V10.C09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Formal groups and Azumaya algebras

### Overview

This section covers two structures that Mathlib has at an early stage. A one dimensional formal group law over a commutative ring $R$ is a power series $F(X, Y) \in R[[X, Y]]$ that behaves like the addition of a group near the identity. The two first examples are the additive law $X + Y$ and the multiplicative law $X + Y + XY$, which is $(1 + X)(1 + Y) - 1$. Formal groups describe the local structure of elliptic curves and of Lie groups, and they are a tool of local class field theory.

An Azumaya algebra over $R$ is an $R$-algebra $A$ that is locally a matrix algebra. Over a field, the Azumaya algebras are the central simple algebras, and their classes form the Brauer group. Mathlib defines Azumaya algebras through the map $A \otimes_R A^{\mathrm{op}} \to \operatorname{End}_R(A)$ and proves that matrix algebras are Azumaya.

### The library around it

#### Formal group laws

The module `Mathlib.RingTheory.FormalGroup.Basic` defines the structure `FormalGroup R` for a commutative ring $R$. Its data is a power series `FormalGroup.toPowerSeries` in `MvPowerSeries (Fin 2) R`, written $F(X, Y)$. The axioms are:

| Lean name | Statement |
|---|---|
| `FormalGroup.zero_constantCoeff` | the constant coefficient of $F$ is $0$ |
| `FormalGroup.lin_coeff_X` | the coefficient of $X$ in $F$ is $1$ |
| `FormalGroup.lin_coeff_Y` | the coefficient of $Y$ in $F$ is $1$ |
| `FormalGroup.assoc` | $F(F(X, Y), Z) = F(X, F(Y, Z))$ |

So $F(X, Y) = X + Y + (\text{terms of degree} \ge 2)$. The associativity axiom uses the substitution of power series, `MvPowerSeries.subst`. The substitution is defined since $F$ has no constant term. The class `FormalGroup.IsComm` adds commutativity, $F(X, Y) = F(Y, X)$, with the field `FormalGroup.comm'`.

The axioms do not include an identity and an inverse. The identity follows. The series `FormalGroup.Xzero` is $F(X, 0)$, and `FormalGroup.zeroX` is $F(0, X)$. The result `FormalGroup.Xzero_eq_X` says that $F(X, 0) = X$, and `FormalGroup.zeroX_eq_X` says that $F(0, X) = X$. So $0$ is a two sided identity for $F$.

**Proof of `FormalGroup.Xzero_eq_X`.** Put $f(X) = F(X, 0)$. Then $f$ has no constant term and its coefficient of $X$ is $1$, `FormalGroup.coeff_one_Xzero`. So $f$ has an inverse $g$ for substitution, with $f(g(X)) = X$. Put $Y = Z = 0$ in the associativity axiom: $F(F(X, 0), 0) = F(X, F(0, 0))$. The constant term of $F$ is $0$, so $F(0, 0) = 0$, and this is $f(f(X)) = f(X)$, `FormalGroup.Xzero_subst_Xzero`. Substitute $g$ for $X$: $f(X) = X$. $\square$

#### Examples and maps

The additive formal group `FormalGroup.𝔾ₐ` is $X + Y$, `FormalGroup.𝔾ₐ_toPowerSeries`. The multiplicative formal group `FormalGroup.𝔾ₘ` is $X + Y + XY$, `FormalGroup.𝔾ₘ_toPowerSeries`. Both are commutative, `FormalGroup.instIsComm𝔾ₐ` and `FormalGroup.instIsComm𝔾ₘ`. For $\mathbb{G}_m$, put $u = 1 + X$ and $v = 1 + Y$. Then $1 + F(X, Y) = uv$, so the associativity of $F$ follows from the associativity of the product. Both sides of the axiom are $(1 + X)(1 + Y)(1 + Z) - 1$.

A ring map $f : R \to S$ moves a formal group over $R$ to one over $S$, `FormalGroup.map`, by applying $f$ to the coefficients. Its series is given by `FormalGroup.map_toPowerSeries`. Two formal groups are equal when their power series are equal, `FormalGroup.ext`.

#### Points

The type `FormalGroup.Point F σ` gives a group from $F$. Its elements are the power series in the variables $\sigma$ over $R$ that can be put into a power series, that is, the series with a nilpotent constant coefficient. The sum of two points $a$ and $b$ is $F(a, b)$, `FormalGroup.add_apply`, and the zero point is $0$, `FormalGroup.zero_apply`. The result is an additive monoid, `FormalGroup.instAddMonoidPoint`, and a commutative one when $F$ is commutative, `FormalGroup.instAddCommMonoidPointOfIsComm`. The identity laws are `FormalGroup.add_zero` and `FormalGroup.zero_add`, from `FormalGroup.Xzero_eq_X` and `FormalGroup.zeroX_eq_X`.

For $\mathbb{G}_m$ the point $a$ corresponds to the unit $1 + a$, and the sum is the product of units. For $\mathbb{G}_a$ the sum is the usual sum. Mathlib does not yet have the inverse of a formal group law, homomorphisms of formal groups, or the logarithm over a $\mathbb{Q}$-algebra.

#### Azumaya algebras

The module `Mathlib.Algebra.Azumaya.Defs` defines the map `AlgHom.mulLeftRight R A` from $A \otimes_R A^{\mathrm{op}}$ to $\operatorname{End}_R(A)$. It sends $a \otimes b$ to the map $x \mapsto axb$, `AlgHom.mulLeftRight_apply`. The class `IsAzumaya R A` asks that $A$ is a finite, projective and faithful $R$-module, and that `AlgHom.mulLeftRight R A` is bijective, `IsAzumaya.bij`. The three module conditions are the parent classes `IsAzumaya.toFinite`, `IsAzumaya.toProjective` and `IsAzumaya.toFaithfulSMul`.

Other characterizations exist in the literature: $A$ is Azumaya when it is central and separable over $R$, or when it gives a Morita equivalence between $R$ and $A \otimes_R A^{\mathrm{op}}$. These are not yet in Mathlib.

| Lean name | Statement |
|---|---|
| `IsAzumaya.id` | $R$ is an Azumaya algebra over itself |
| `IsAzumaya.tensorEquivEnd` | the isomorphism $R \otimes_R R^{\mathrm{op}} \cong \operatorname{End}_R(R)$ |
| `IsAzumaya.of_AlgEquiv` | an algebra isomorphic to an Azumaya algebra is Azumaya |
| `IsAzumaya.matrix` | the matrix algebra $M_n(R)$ is Azumaya for $n$ nonempty and finite |
| `Algebra.IsCentral.instIsAzumaya` | a free Azumaya algebra is central |

The module `Mathlib.Algebra.Azumaya.Basic` has the first two results and the transport `IsAzumaya.of_AlgEquiv`, with the compatibility `IsAzumaya.mulLeftRight_comp_congr` of the map with an isomorphism. The module `Mathlib.Algebra.Azumaya.Matrix` has `IsAzumaya.matrix`. The inverse of the map for matrices is `AlgHom.mulLeftRightMatrix_inv`, and `AlgHom.mulLeftRightMatrix.inv_comp` and `AlgHom.mulLeftRightMatrix.comp_inv` say that it is a two sided inverse.

**Proof sketch of `IsAzumaya.matrix`.** The algebra $M_n(R)$ is free of rank $n^2$, so it is finite, projective and faithful. Let $E_{ij}$ be the matrix units. The map sends $E_{ij} \otimes E_{kl}$ to the endomorphism $X \mapsto E_{ij}XE_{kl}$, which sends $E_{jk}$ to $E_{il}$ and the other matrix units to $0$. These $n^4$ endomorphisms are the elementary maps for the basis $(E_{ij})$ of $M_n(R)$. So the map sends a basis of $M_n(R) \otimes_R M_n(R)^{\mathrm{op}}$ to a basis of $\operatorname{End}_R(M_n(R))$, and it is bijective. $\square$

**Proof of `Algebra.IsCentral.instIsAzumaya`.** Let $z$ be in the center of $A$. Then $x \mapsto zx$ commutes with all the maps $x \mapsto axb$, so it is in the center of $\operatorname{End}_R(A)$, since these maps are all of $\operatorname{End}_R(A)$ by bijectivity. For a free module of finite rank, the center of $\operatorname{End}_R(A)$ is $R$. So left multiplication by $z$ is multiplication by some $r \in R$, and $z = z \cdot 1 = r \cdot 1$ is in the image of $R$. $\square$

#### Common errors

1. A formal group law in Mathlib is one dimensional, over a commutative ring. The power series has two variables, indexed by `Fin 2`. The variables are `MvPowerSeries.X 0` and `MvPowerSeries.X 1`, not two separate power series rings.
2. `FormalGroup.Point` is only an additive monoid in this version, not a group. Do not expect a negation on it.
3. The Azumaya condition is about $A^{\mathrm{op}}$, which Mathlib writes with `MulOpposite`. An element of $A \otimes_R A^{\mathrm{op}}$ needs `MulOpposite.op` on the right factor.

### Exercises

1. (A) Show that $X + Y + XY$ satisfies the axioms of `FormalGroup` with the substitution $u = 1 + X$.
2. (A) Use `IsAzumaya.matrix` and `IsAzumaya.of_AlgEquiv` to show that $\operatorname{End}_R(R^n)$ is an Azumaya algebra for $n \ge 1$.
3. (B) Let $c \in R$. Show that $F(X, Y) = X + Y + cXY$ is a commutative formal group law, and that it is $\mathbb{G}_a$ for $c = 0$ and $\mathbb{G}_m$ for $c = 1$.
4. (B) Show that the product algebra $R \times R$ is not Azumaya over $R$ when $R$ is a nontrivial ring. Hint: use `Algebra.IsCentral.instIsAzumaya`.
5. (B) Show that a point of `FormalGroup.Point` for $\mathbb{G}_m$ with $\sigma$ empty is a nilpotent element $a$ of $R$, and that the sum of $a$ and $b$ corresponds to the unit $(1 + a)(1 + b)$.
6. (C) Show that the quaternion algebra $\mathbb{H}$ over $\mathbb{R}$ is Azumaya. Prove that $\mathbb{H} \otimes_{\mathbb{R}} \mathbb{H}^{\mathrm{op}} \to \operatorname{End}_{\mathbb{R}}(\mathbb{H})$ is injective, and compare dimensions.

### Reference

<?reference?>
