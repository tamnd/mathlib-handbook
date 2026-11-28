---
title: Matrix algebras, Morita equivalence and the Orzech property
kind: api
modules:
  - Mathlib.RingTheory.MatrixAlgebra
  - Mathlib.RingTheory.Morita.Basic
  - Mathlib.RingTheory.Morita.Matrix
  - Mathlib.RingTheory.OrzechProperty
  - Mathlib.RingTheory.RingInvo
explains:
  E2: [matrixEquivTensor, Matrix.kroneckerAlgEquiv, Matrix.kroneckerTMulAlgEquiv, MoritaEquivalence, IsMoritaEquivalent, ModuleCat.matrixEquivalence, IsMoritaEquivalent.matrix, OrzechProperty, OrzechProperty.bijective_of_surjective_endomorphism, RingInvo]
  E1: auto
families: []
requires: [V08, V10.C11]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Matrix algebras, Morita equivalence and the Orzech property

### Overview

Matrix algebras are the simplest algebras that are not commutative. For a commutative ring $R$ and an $R$-algebra $A$, the algebra $M_n(A)$ of $n \times n$ matrices over $A$ is a tensor product: $M_n(A) \cong A \otimes_R M_n(R)$. Tensor products of matrix algebras are matrix algebras, through the Kronecker product: $M_m(R) \otimes_R M_n(R) \cong M_{mn}(R)$. These isomorphisms are the basic tools for Azumaya algebras in Chapter 11.

A ring $R$ and the ring $M_n(R)$ have the same modules, in a precise sense: their module categories are equivalent. Two algebras with equivalent module categories are Morita equivalent. Mathlib defines Morita equivalence over a base ring and proves that $R$ is Morita equivalent to $M_n(R)$ for $n \ge 1$.

This section also treats two smaller topics. The Orzech property of a ring says that a surjection from a submodule of a finitely generated module onto the module is injective. It holds for commutative rings and for Noetherian rings, and it gives the strong rank condition. A ring involution is an anti-automorphism of order $2$, such as the transpose on matrices over a commutative ring.

### The library around it

#### Matrices as tensor products

The module `Mathlib.RingTheory.MatrixAlgebra` contains the algebra isomorphisms between matrix algebras and tensor products.

| Lean name | Statement |
|---|---|
| `matrixEquivTensor n R A` | $M_n(A) \cong A \otimes_R M_n(R)$ as $R$-algebras |
| `Matrix.kroneckerAlgEquiv m n R` | $M_m(R) \otimes_R M_n(R) \cong M_{m \times n}(R)$ |
| `Matrix.kroneckerTMulAlgEquiv m n R S A B` | $M_m(A) \otimes_R M_n(B) \cong M_{m \times n}(A \otimes_R B)$ |
| `kroneckerLinearEquiv l m n p R` | the linear form for rectangular matrices |
| `kroneckerTMulLinearEquiv` | the linear form with coefficients in modules |

The map `matrixEquivTensor` sends the matrix unit $E_{ij}(x)$ with entry $x$ at $(i, j)$ to $x \otimes E_{ij}$, by `matrixEquivTensor_apply_single`. Its inverse sends $a \otimes M$ to $a \cdot M$, where $M$ is mapped into $M_n(A)$ entry by entry, `matrixEquivTensor_apply_symm`. The proof of bijectivity builds the inverse `MatrixEquivTensor.invFun` explicitly and checks `MatrixEquivTensor.left_inv` and `MatrixEquivTensor.right_inv`.

The Kronecker maps send $x \otimes y$ to the Kronecker product `Matrix.kroneckerMap`, by `kroneckerLinearEquiv_tmul`. For $x \in M_m(R)$ and $y \in M_n(R)$, the Kronecker product is the matrix with entries $x_{ii'}y_{jj'}$ at the index $((i, j), (i', j'))$. The rule $(x \otimes y)(x' \otimes y') = xx' \otimes yy'$ shows that this is multiplicative. The star versions `Matrix.kroneckerStarAlgEquiv` and `Matrix.kroneckerTMulStarAlgEquiv` also respect the conjugate transpose.

#### Morita equivalence

The module `Mathlib.RingTheory.Morita.Basic` defines `MoritaEquivalence R A B` for two $R$-algebras $A$ and $B$. It is a structure that holds an equivalence of categories `ModuleCat A ≌ ModuleCat B`, the field `MoritaEquivalence.eqv`, with the condition that the functor is $R$-linear. The predicate `IsMoritaEquivalent R A B` says that such an equivalence exists.

Morita equivalence is an equivalence relation.

1. `IsMoritaEquivalent.refl` gives reflexivity.
2. `IsMoritaEquivalent.symm` uses the inverse equivalence.
3. `IsMoritaEquivalent.trans` composes the equivalences.

Isomorphic algebras are Morita equivalent, `IsMoritaEquivalent.of_algEquiv`, through `MoritaEquivalence.ofAlgEquiv`.

#### Matrix rings

**Theorem.** Let $R$ be a ring, $\iota$ a nonempty finite type and $i \in \iota$. The functor $M \mapsto M^\iota$ is an equivalence from $R$-modules to $M_\iota(R)$-modules. Its inverse sends $N$ to $E_{ii}N$.

The equivalence is `ModuleCat.matrixEquivalence R i` in `Mathlib.RingTheory.Morita.Matrix`. So $R$ and $M_\iota(R)$ are Morita equivalent over each commutative ring $R_0$ with an algebra map to $R$, `IsMoritaEquivalent.matrix`.

*Proof sketch.* The matrices act on $M^\iota$ by the product of a matrix and a column vector. This is the functor `ModuleCat.toMatrixModCat`. In the other direction, $E_{ii}N$ is a submodule `MatrixModCat.toModuleCatObj` over $R$, with the description `MatrixModCat.mem_toModuleCatObj`. For an $R$-module $M$, the map $x \mapsto E_{ii}(x)$, the vector with $x$ in position $i$, gives $M \cong E_{ii}M^\iota$. This is the unit `MatrixModCat.unitIso`. For an $M_\iota(R)$-module $N$, the map $y \mapsto (E_{ij}y)_j$ gives $N \cong (E_{ii}N)^\iota$, since $\sum_j E_{jj} = 1$. This is the counit `MatrixModCat.counitIso`. $\square$

**Example.** Let $\iota = \{1, 2\}$ and $M = R$. The functor gives the module $R^2$ of column vectors over $M_2(R)$. In the other direction, $E_{11}R^2$ is the set of vectors $(x, 0)$, a copy of $R$. The module $R^2$ is a simple $M_2(K)$-module for a field $K$, and it corresponds to the simple $K$-module $K$.

Many properties of rings that are defined through modules are therefore invariant under passage to matrix rings: the property that all modules are projective, the Noetherian property, and simplicity. The library does not yet state these transfers.

#### The Orzech property

The class `OrzechProperty R` in `Mathlib.RingTheory.OrzechProperty` says the following: for each finitely generated module $M$ and each submodule $N \subseteq M$, each surjective linear map $N \to M$ is injective. The form for a submodule is `OrzechProperty.injective_of_surjective_of_submodule`, and `orzechProperty_iff` restates the definition.

**Corollary.** Over a ring with the Orzech property, a surjective endomorphism of a finitely generated module is bijective.

This is `OrzechProperty.bijective_of_surjective_endomorphism`. The more general form `OrzechProperty.injective_of_surjective_of_injective` takes an injective $i : N \to M$ and a surjective $f : N \to M$, and proves that $f$ is injective.

Three classes of rings have the property.

1. Finite rings, by the instance `OrzechProperty.instOfFinite`. A surjection between finite sets of the same size is a bijection, and $|N| \le |M|$.
2. Commutative rings, `CommRing.orzechProperty`. The proof reduces to a finitely generated subring, which is Noetherian, and then uses the third case.
3. Left Noetherian rings, `IsNoetherianRing.orzechProperty`.

For a nontrivial ring, the Orzech property gives the strong rank condition, `strongRankCondition_of_orzechProperty`: if there is an injective linear map $R^n \to R^m$, then $n \le m$. So `StrongRankCondition` holds for each nontrivial commutative ring, and the rank of a free module is well defined.

#### Ring involutions

The structure `RingInvo R` in `Mathlib.RingTheory.RingInvo` is a ring isomorphism $\sigma : R \to R^{\mathrm{op}}$ with $\sigma(\sigma(x)) = x$, the field `RingInvo.involution`. So $\sigma$ is additive, $\sigma(xy) = \sigma(y)\sigma(x)$, and $\sigma$ is its own inverse. The constructor `RingInvo.mk'` takes a ring map $R \to R^{\mathrm{op}}$ and a proof of the involution law. For a commutative ring, the identity is an involution, `RingInvo.id`. The class `RingInvoClass` is for types of bundled involutions. An involution maps only $0$ to $0$, `RingInvo.map_eq_zero_iff`.

#### Common errors

1. `matrixEquivTensor` puts $A$ on the left of the tensor product. The order matters when it is composed with other equivalences, and `Algebra.TensorProduct.comm` swaps the factors.
2. `IsMoritaEquivalent.matrix` needs `Nonempty ι`. For the empty type, $M_\iota(R)$ is the zero ring, which is not Morita equivalent to a nonzero ring.
3. `IsMoritaEquivalent.trans` needs the three algebras in the same universe, since the module categories are compared in one universe.

### Exercises

1. (A) Write the image of $E_{12}(x)$ under `matrixEquivTensor` for $n = 2$, and check that the product $E_{12}(x)E_{21}(y)$ maps to the product of the images.
2. (A) Show that the transpose on $M_n(R)$ is a ring involution for a commutative ring $R$, and give the data for `RingInvo.mk'`.
3. (B) Show that $M_2(R) \otimes_R M_3(R) \cong M_6(R)$ with `Matrix.kroneckerAlgEquiv`, and compute the Kronecker product of $E_{11}$ and $E_{23}$.
4. (B) Show that the shift $(a_0, a_1, a_2, \dots) \mapsto (a_1, a_2, \dots)$ on $\mathbb{Z}^{\mathbb{N}}$ is surjective but not injective. Explain why this does not contradict `OrzechProperty.bijective_of_surjective_endomorphism`.
5. (B) Prove that a Morita equivalence between $R$-algebras $A$ and $B$ sends a projective $A$-module to a projective $B$-module.
6. (C) Prove that if $A$ and $B$ are Morita equivalent commutative rings, then $A \cong B$. Use the center of the endomorphism ring of the identity functor.

### Reference

<?reference?>
