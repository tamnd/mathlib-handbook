---
title: The general linear group
kind: api
modules:
  - Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
  - Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
  - Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
  - Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
  - Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
  - Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
  - Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.MvPolynomial
  - Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
explains:
  E2: [LinearMap.GeneralLinearGroup, LinearMap.GeneralLinearGroup.generalLinearEquiv, LinearEquiv.conjAlgEquiv_surjective, Matrix.GeneralLinearGroup, Matrix.GeneralLinearGroup.det, Matrix.GeneralLinearGroup.toLin, Matrix.GLPos, Matrix.GeneralLinearGroup.center_eq_range_scalar, Matrix.card_GL_field, Matrix.ProjGenLinGroup]
  E1: auto
families: []
requires: [V03, V05, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The general linear group

### Overview

The invertible linear maps of a module $M$ to itself make a group under composition. This group is the general linear group of $M$. When $M = R^n$ for a commutative ring $R$, the same group is the group of the invertible $n \times n$ matrices, which is $GL_n(R)$. Mathlib has the two forms. `LinearMap.GeneralLinearGroup R M` is the group of units of the ring of endomorphisms, for each module. `Matrix.GeneralLinearGroup n R`, with the notation `GL n R`, is the group of units of the matrix ring. This section gives the two definitions and the equivalences between them, the determinant as a group homomorphism, the subgroup of matrices with positive determinant, the center and the projective group, the number of elements over a finite field, and the classification of $2 \times 2$ matrices by their discriminant.

### The library around it

#### The general linear group of a module

**Definition (`LinearMap.GeneralLinearGroup`).** For a semiring $R$ and an $R$-module $M$, `LinearMap.GeneralLinearGroup R M` is the group of units of the monoid `Module.End R M`.

An element is a linear map $f : M \to M$ together with a linear map $g$ such that $f \circ g = g \circ f = \mathrm{id}$. Thus an element is the same as a linear equivalence of $M$ with itself.

**Definition (`LinearMap.GeneralLinearGroup.generalLinearEquiv`).** `LinearMap.GeneralLinearGroup.generalLinearEquiv R M` is the group isomorphism from `LinearMap.GeneralLinearGroup R M` to the group `M ≃ₗ[R] M` of linear automorphisms.

The two directions are `LinearMap.GeneralLinearGroup.toLinearEquiv` and `LinearMap.GeneralLinearGroup.ofLinearEquiv`. Use the first form when the computation is in the ring `Module.End R M`, and use the second form when the inverse map must be evaluated. A semilinear equivalence $e : M_1 \simeq M_2$ gives the isomorphism `LinearMap.GeneralLinearGroup.congrLinearEquiv e`, which sends $f$ to $e \circ f \circ e^{-1}$.

Each unit of `Module.End R M` acts on `Module.End R M` by conjugation, and this action is by algebra automorphisms. Over a field, each algebra automorphism has this form.

**Theorem (`LinearEquiv.conjAlgEquiv_surjective`).** Let $K$ be a semifield and $V$, $W$ projective $K$-modules. Then each algebra isomorphism $\varphi$ from `Module.End K V` to `Module.End K W` has the form $\varphi(x) = T \circ x \circ T^{-1}$ for a linear isomorphism $T : V \simeq W$.

*Proof sketch.* If $V$ is the zero module, then $0 = 1$ in `Module.End K V`, so $0 = 1$ in `Module.End K W` and $W$ is also the zero module. Otherwise, select a nonzero vector $u$ and a linear form $v$ with $v(u) \ne 0$, which exists because $V$ is projective. For $x$ in $V$, let $r_x$ be the rank one map $y \mapsto v(y) x$. Select $z$ in $W$ with $\varphi(r_u)(z) \ne 0$, and put $T(x) = \varphi(r_x)(z)$. Then $T$ is linear, and $r_{A x} = A \circ r_x$ gives $T(A x) = \varphi(A)(T x)$ for each endomorphism $A$. A second linear form on $W$ shows that $T$ is surjective, and the relation shows that $T$ is injective. $\square$

This is a form of the theorem of Skolem and Noether for the endomorphism algebras. The version for one module, `Module.End.mulSemiringActionToAlgEquiv_conjAct_surjective`, says that the map from `LinearMap.GeneralLinearGroup K V` to the group of algebra automorphisms of `Module.End K V` is surjective.

#### The matrix group

**Definition (`Matrix.GeneralLinearGroup`).** For a finite type $n$ with decidable equality and a semiring $R$, `Matrix.GeneralLinearGroup n R` is the group of units of the ring `Matrix n n R`. The notation is `GL n R`.

An element `A : GL n R` has the underlying matrix `↑A` and the inverse matrix `↑A⁻¹`. Over a commutative ring, `↑A⁻¹` is the inverse matrix of Chapter 4 Section 2 (`Matrix.GeneralLinearGroup.coe_inv`). Two elements are equal when their entries are equal (`Matrix.GeneralLinearGroup.ext_iff`). The usual ways to make an element from a matrix $A$ are `Matrix.GeneralLinearGroup.mk'` from an instance `Invertible A.det`, `Matrix.GeneralLinearGroup.mk''` from a proof of `IsUnit A.det`, and, over a field, `Matrix.GeneralLinearGroup.mkOfDetNeZero` from a proof of $\det A \ne 0$. An example is `Matrix.planeConformalMatrix a b`, the matrix `!![a, -b; b, a]` over a field when $a^2 + b^2 \ne 0$.

**Definition (`Matrix.GeneralLinearGroup.det`).** Over a commutative ring $R$, `Matrix.GeneralLinearGroup.det` is the group homomorphism from `GL n R` to the group of units $R^\times$ that sends $A$ to $\det A$.

The determinant of an invertible matrix is a unit by Chapter 4 Section 2, and the multiplicativity of the determinant makes this map a homomorphism. The value as an element of $R$ is given by `Matrix.GeneralLinearGroup.val_det_apply`. If $n$ is not empty, the homomorphism is surjective (`Matrix.GeneralLinearGroup.det_surjective`): the diagonal matrix with $u$ in one entry and $1$ in the others has determinant $u$. Its kernel is the special linear group of Section 2 (`Matrix.SpecialLinearGroup.range_toGL_eq_ker_det` and `Matrix.SpecialLinearGroup.toGLKerEquiv`).

The scalar matrices give the homomorphism `Matrix.GeneralLinearGroup.scalar n` from $R^\times$ to `GL n R`, and `Matrix.GeneralLinearGroup.det_scalar` says that $\det(u \cdot 1) = u^{|n|}$.

The two forms of the general linear group agree for the module $R^n$, and for each module with a basis indexed by $n$.

**Definition (`Matrix.GeneralLinearGroup.toLin`).** Over a commutative ring $R$, `Matrix.GeneralLinearGroup.toLin` is the group isomorphism from `GL n R` to `LinearMap.GeneralLinearGroup R (n → R)` that sends a matrix to its linear map $v \mapsto A v$.

For a basis $b$ of a module $V$ indexed by $n$, `Matrix.GeneralLinearGroup.toLin' b` is the group isomorphism from `GL n R` to `LinearMap.GeneralLinearGroup R V` given by the matrices in the basis $b$ of Chapter 3.

The constructions of Chapter 3 pass to the group. A ring homomorphism $f : R \to S$ gives `Matrix.GeneralLinearGroup.map f`, and a ring isomorphism gives `Matrix.GeneralLinearGroup.mapEquiv`. An equivalence $m \simeq n$ gives the isomorphism `Matrix.GeneralLinearGroup.reindex`. The transpose is an isomorphism `Matrix.GeneralLinearGroup.transposeMulEquiv` from `GL n R` to its opposite group, because $(AB)^T = B^T A^T$. The Kronecker product of two invertible matrices is invertible, and `Matrix.GeneralLinearGroup.kronecker` gives the element of `GL (n × m) R`.

#### Matrices with positive determinant

**Definition (`Matrix.GLPos`).** Over a linearly ordered commutative ring $R$, `Matrix.GLPos n R` is the subgroup of `GL n R` of the matrices with $\det A > 0$.

The membership lemma is `Matrix.mem_glpos`, and the scoped notation `GL(n, R)⁺` in the namespace MatrixGroups means `Matrix.GLPos (Fin n) R`. The subgroup is the kernel of the sign of the determinant, so it has index $2$ in `GL n R` when $n$ is not empty. The matrix $-A$ has determinant $(-1)^{|n|} \det A$. Thus, when $|n|$ is even, `Matrix.GLPos n R` has a negation, and `Matrix.GLPos.coe_neg` says that its underlying matrix is $-A$. The special linear group maps into this subgroup by `Matrix.SpecialLinearGroup.toGLPos`.

#### The center and the projective group

**Theorem (`Matrix.GeneralLinearGroup.center_eq_range_scalar`).** Over a commutative ring $R$, the center of `GL n R` is the image of `Matrix.GeneralLinearGroup.scalar n`, that is, the group of the scalar matrices $u \cdot 1$ with $u$ a unit.

*Proof sketch.* A scalar matrix commutes with each matrix. Conversely, let $g$ be in the center. Then $g$ commutes with each transvection $1 + c E_{ij}$ for $i \ne j$, so its underlying matrix is a scalar matrix $a \cdot 1$ (`Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar`). The same argument for $g^{-1}$ gives a scalar $b$ with $a b = 1$, so $a$ is a unit. $\square$

**Definition (`Matrix.ProjGenLinGroup`).** Over a commutative ring $R$, `Matrix.ProjGenLinGroup n R` is the quotient of `GL n R` by its center. The scoped notation is `PGL(n, R)` in the namespace MatrixGroups.

The quotient map is `Matrix.ProjGenLinGroup.mk`. It is surjective (`Matrix.ProjGenLinGroup.mk_surjective`), and two matrices have the same image if and only if they differ by a scalar unit (`Matrix.ProjGenLinGroup.mk_eq_mk_iff`). A homomorphism from `GL n R` that is trivial on the scalar matrices passes to the quotient by `Matrix.ProjGenLinGroup.lift`. In the same way, an action of `GL n R` in which the scalar matrices act trivially gives an action of the projective group (`Matrix.ProjGenLinGroup.mulActionOfGL`). A ring homomorphism gives `Matrix.ProjGenLinGroup.map`. Over an ordered ring and for $|n|$ even, the sign of the determinant does not change when the matrix is multiplied by a scalar, so it gives the homomorphism `Matrix.ProjGenLinGroup.signDet`.

The projective special linear group of Section 2 maps into the projective general linear group by `Matrix.ProjectiveSpecialLinearGroup.toPGL`, and this map is injective (`Matrix.ProjectiveSpecialLinearGroup.toPGL_injective`). It is surjective if and only if each unit of $R$ has a root of order $|n|$ (`Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_iff`). Thus over an algebraically closed field the two groups are isomorphic (`Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed`).

#### Counting over a finite field

**Theorem (`Matrix.card_GL_field`).** Let $\mathbb{F}$ be a finite field with $q$ elements. Then the number of elements of `GL (Fin n) 𝔽` is $\prod_{i=0}^{n-1} (q^n - q^i)$.

*Proof sketch.* A matrix is invertible if and only if its columns are linearly independent, so `Matrix.equiv_GL_linearindependent` is an equivalence between `GL (Fin n) 𝔽` and the families of $n$ linearly independent vectors in $\mathbb{F}^n$. Count these families column by column. When the first $i$ columns are fixed, they span a subspace with $q^i$ elements, and the next column can be each of the other $q^n - q^i$ vectors. This is `card_linearIndependent`. $\square$

The determinant is surjective with kernel $SL_n$, so the special linear group has $\prod_{i=0}^{n-1} (q^n - q^i) / (q - 1)$ elements (`Matrix.card_SL_field`), and over each finite commutative ring `Matrix.card_SL_mul_card_units` gives the product formula. The number of all the matrices is `Matrix.card_matrix`.

The module `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.MvPolynomial` holds one theorem, which is not in the index of this handbook: two polynomials in the $n^2$ entries over an infinite field are equal if their values agree at each invertible matrix. The invertible matrices are dense for the Zariski topology.

#### Matrices of size two

For a $2 \times 2$ matrix $m$, the discriminant `Matrix.discr m` is $\operatorname{tr}(m)^2 - 4 \det m$ (`Matrix.discr_fin_two`). It is the discriminant of the characteristic polynomial of Chapter 5, and it does not change under conjugation. The module `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo` classifies $2 \times 2$ matrices by it.

- `Matrix.IsParabolic m`: $m$ is not a scalar matrix and its discriminant is $0$.
- `Matrix.IsHyperbolic m`: the discriminant is positive, over an ordered ring.
- `Matrix.IsElliptic m`: the discriminant is negative, over an ordered ring.

The three conditions are invariant under conjugation by `GL (Fin 2) R` (`Matrix.isParabolic_conj_iff`, `Matrix.isHyperbolic_conj_iff`, `Matrix.isElliptic_conj_iff`) and under negation (`Matrix.isParabolic_neg_iff`). The versions with the prefix `Matrix.GeneralLinearGroup` apply to group elements. Over a field in which $2 \ne 0$, a parabolic matrix has one eigenvalue $\lambda = \operatorname{tr}(m)/2$ (`Matrix.parabolicEigenvalue`), and $(m - \lambda)^2 = 0$ (`Matrix.IsParabolic.sub_eigenvalue_sq_eq_zero`). Thus $m$ is a scalar plus a nonzero nilpotent matrix (`Matrix.isParabolic_iff_exists`). The upper triangular unipotent matrices give the homomorphism `Matrix.GeneralLinearGroup.upperRightHom` from the additive group of $R$, with value `!![1, x; 0, 1]` at $x$. These definitions prepare the study of the modular group in the chapter on modular forms of Volume 12.

#### Common errors

1. `GL n R` takes the index type first and the ring second, but `LinearMap.GeneralLinearGroup R M` takes the ring first. Also `GL 2 R` is not `GL (Fin 2) R`: with a natural number, use `GL (Fin 2) R`.
2. An element `A : GL n R` is not a matrix. Use the coercion `↑A` for the matrix, and use `Matrix.GeneralLinearGroup.ext_iff` to compare two elements by their entries.
3. `Matrix.GeneralLinearGroup.det A` is a unit of $R$, not an element of $R$. To get the element `(↑A).det`, apply the coercion and rewrite with `Matrix.GeneralLinearGroup.val_det_apply`.

### Exercises

1. (A) Make the element `!![2, 1; 1, 1]` of `GL (Fin 2) ℤ` with `Matrix.GeneralLinearGroup.mk''`, and compute its inverse.
2. (A) Show that `Matrix.GeneralLinearGroup.det` of `Matrix.GeneralLinearGroup.scalar n u` is $u^{|n|}$ for $|n| = 3$.
3. (B) Use `Matrix.card_GL_field` to show that `GL (Fin 2) (ZMod 2)` has $6$ elements, and give an isomorphism with the symmetric group on three letters.
4. (B) Show that the matrix `!![1, 1; 0, 1]` over $\mathbb{Q}$ is parabolic and that `!![0, -1; 1, 0]` over $\mathbb{Q}$ is elliptic.
5. (B) Show that the center of `GL (Fin 2) ℤ` has two elements.
6. (C) Show that `Matrix.GLPos (Fin 1) ℝ` is isomorphic to the multiplicative group of the positive reals, and that the index of `Matrix.GLPos (Fin n) ℝ` in `GL (Fin n) ℝ` is $2$ for $n \ge 1$.

### Reference

<?reference?>
