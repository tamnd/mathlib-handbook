---
title: Matrices of bilinear and sesquilinear forms
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.Bilinear
  - Mathlib.LinearAlgebra.Matrix.BilinearForm
  - Mathlib.LinearAlgebra.Matrix.SesquilinearForm
  - Mathlib.LinearAlgebra.Matrix.Nondegenerate
  - Mathlib.LinearAlgebra.Basis.Bilinear
  - Mathlib.LinearAlgebra.Quotient.Bilinear
explains:
  E2: [Matrix.toLinearMap₂', LinearMap.toMatrix₂, LinearMap.toMatrix₂_mul_basis_toMatrix, Matrix.toBilin, LinearMap.BilinForm.nondegenerate_iff_det_ne_zero, Matrix.SeparatingLeft, Matrix.Nondegenerate, Matrix.IsAdjointPair, LinearMap.ext_basis, LinearMap.liftQ₂]
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

## Matrices of bilinear and sesquilinear forms

### Overview

A linear map $V \to W$ has a matrix in a choice of bases, and Chapter 3 Section 3 makes this a linear equivalence. A bilinear map $B : M_1 \times M_2 \to N$ also has a matrix: its entry at $(i, j)$ is $B(b_i, c_j)$ for bases $(b_i)$ of $M_1$ and $(c_j)$ of $M_2$. The value of $B$ at two vectors is then $x^T A y$, with $x$ and $y$ the coordinate vectors. This section describes the equivalence between bilinear maps and matrices in Mathlib, the change of the matrix under a change of bases, and the matrix form of nondegeneracy.

The general theory of bilinear and sesquilinear forms, such as orthogonality and the adjoint of a map, is in Volume 8 Chapter 5. Here a bilinear map is a term of the type `M₁ →ₗ[R] M₂ →ₗ[R] N`, a linear map into a space of linear maps, and a bilinear form is the case `LinearMap.BilinForm R M` with $M_1 = M_2 = M$ and $N = R$. A sesquilinear map is the same with semilinear maps `M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] N`, for example linear in one argument and conjugate linear in the other.

### The library around it

#### The matrix of a bilinear map

Mathlib states the main equivalence first for the standard spaces $n \to R$ and $m \to R$.

**Definition (`Matrix.toLinearMap₂'`).** For finite types $n$ and $m$ and a module $N$ over a commutative semiring $R$, `Matrix.toLinearMap₂' R` is the linear equivalence from the matrices of type `Matrix n m N` to the bilinear maps $(n \to R) \to (m \to R) \to N$, with $B(x, y) = \sum_i \sum_j x_i y_j M_{ij}$.

The formula is `Matrix.toLinearMap₂'_apply`, and for $N = R$ the lemma `Matrix.toLinearMap₂'_apply'` writes the value as the dot product $x \cdot (M y)$. The entry is the value at two standard basis vectors (`Matrix.toLinearMap₂'_single`). The inverse is `LinearMap.toMatrix₂'`, with `LinearMap.toMatrix₂'_apply` for its entries. The semilinear forms are `Matrix.toLinearMapₛₗ₂'` and `LinearMap.toMatrixₛₗ₂'`, with the ring homomorphisms $\sigma_1$ and $\sigma_2$ applied to the coordinates (`Matrix.toLinearMapₛₗ₂'_apply`).

For modules with bases there is the same equivalence.

**Definition (`LinearMap.toMatrix₂`).** For a basis $b_1$ of $M_1$ indexed by $n$ and a basis $b_2$ of $M_2$ indexed by $m$, `LinearMap.toMatrix₂ b₁ b₂` is the linear equivalence from the bilinear maps $M_1 \to M_2 \to N$ to `Matrix n m N` with the entry $B(b_1(i), b_2(j))$ at $(i, j)$.

The entry formula is `LinearMap.toMatrix₂_apply`. The inverse is `Matrix.toLinearMap₂`, and the round trips are `LinearMap.toMatrix₂_toLinearMap₂` and `Matrix.toLinearMap₂_toMatrix₂`. For the standard bases, `LinearMap.toMatrix₂_basisFun` says that the general version is the primed version. The lemma `apply_eq_dotProduct_toMatrix₂_mulVec`, in the root namespace, writes $B(x, y)$ as a dot product of the coordinate vectors with the matrix, after the ring homomorphisms are applied.

A bilinear map is determined by its values on the basis vectors, which is the reason for the equivalence.

**Theorem (`LinearMap.ext_basis`).** Let $b_1$ and $b_2$ be bases of $M_1$ and $M_2$. If two sesquilinear maps $B$ and $B'$ satisfy $B(b_1(i), b_2(j)) = B'(b_1(i), b_2(j))$ for all $i$ and $j$, then $B = B'$.

*Proof.* For a fixed $i$, the two linear maps $B(b_1(i), \cdot)$ and $B'(b_1(i), \cdot)$ agree on the basis $b_2$, so they are equal. Then the two linear maps $B$ and $B'$ from $M_1$ agree on the basis $b_1$, so they are equal. $\square$

The form with an equivalence is `LinearMap.ext_iff_basis`, and the version for bilinear forms is `LinearMap.BilinForm.ext_iff_basis`. The expansion `LinearMap.sum_repr_mul_repr_mul` writes $B(x, y)$ as the double sum $\sum_{i,j} x_i y_j B(b_1(i), b_2(j))$ over the coordinates of $x$ and $y$.

#### Change of bases

A composition with linear maps on the two sides changes the matrix by products.

**Theorem (`LinearMap.toMatrix₂_compl₁₂`).** For linear maps $l : M_1' \to M_1$ and $r : M_2' \to M_2$, the matrix of $(x, y) \mapsto B(l x, r y)$ is $L^T A R$, where $A$ is the matrix of $B$ and $L$ and $R$ are the matrices of $l$ and $r$.

*Proof.* The entry at $(i, j)$ of the matrix of the composition is $B(l(b_1'(i)), r(b_2'(j)))$. Write $l(b_1'(i)) = \sum_k L_{ki} b_1(k)$ and $r(b_2'(j)) = \sum_s R_{sj} b_2(s)$, and expand by bilinearity: the value is $\sum_{k, s} L_{ki} A_{ks} R_{sj}$, the entry of $L^T A R$. $\square$

The one sided versions are `LinearMap.toMatrix₂_comp` and `LinearMap.toMatrix₂_compl₂`, and `LinearMap.mul_toMatrix₂_mul` is the converse direction, which writes $M A N$ as the matrix of a composition. With the identity maps and two pairs of bases, the result is the change of basis formula.

**Theorem (`LinearMap.toMatrix₂_mul_basis_toMatrix`).** Let $b_1, c_1$ be bases of $M_1$ and $b_2, c_2$ bases of $M_2$, and let $P_1$ and $P_2$ be the change of basis matrices `b₁.toMatrix c₁` and `b₂.toMatrix c₂` of Chapter 3 Section 3. Then the matrix of $B$ in the bases $c_1, c_2$ is $P_1^T A P_2$, where $A$ is the matrix in the bases $b_1, b_2$.

So the matrix of a bilinear map changes by congruence, $A \mapsto P^T A P$, and not by similarity, $A \mapsto P^{-1} A P$, as for a linear endomorphism. This is why the determinant of the matrix of a bilinear form is defined only up to the square of a unit.

#### Bilinear forms

For a bilinear form $B : M \to M \to R$ with one basis $b$ of $M$, the module `Mathlib.LinearAlgebra.Matrix.BilinearForm` gives the special case of the equivalence above.

**Definition (`Matrix.toBilin`).** For a basis $b$ of $M$ indexed by $n$, `Matrix.toBilin b` is the linear equivalence from `Matrix n n R` to `LinearMap.BilinForm R M` with $B(x, y) = \sum_{i,j} x_i M_{ij} y_j$, where $x_i$ and $y_j$ are the coordinates in $b$.

The inverse is `LinearMap.BilinForm.toMatrix b`, with the entries `LinearMap.BilinForm.toMatrix_apply`. The standard versions are `Matrix.toBilin'` and `LinearMap.BilinForm.toMatrix'`, with `Matrix.toBilin'_apply'`, $B(v, w) = v \cdot (M w)$. The change of basis formula is `LinearMap.BilinForm.toMatrix_mul_basis_toMatrix`, and the formula for compositions is `LinearMap.BilinForm.toMatrix_comp`. A bilinear form is symmetric if and only if its matrix is symmetric (`LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm`, `Matrix.isSymm_toBilin_iff_isSymm`), with the class `Matrix.IsSymm` of Chapter 3 Section 7.

The module `Mathlib.LinearAlgebra.Matrix.Bilinear` treats a different bilinear map: the product of matrices. The definition `mulLinearMap` is the product $(X, Y) \mapsto X Y$ as a bilinear map of matrices over an algebra $A$, and `mulLeftLinearMap` and `mulRightLinearMap` are the linear maps $Y \mapsto X Y$ and $X \mapsto X Y$. The lemmas `mulLeftLinearMap_mul` and `pow_mulLeftLinearMap` say that these maps respect products and powers, and `commute_mulLeftLinearMap_mulRightLinearMap` says that left and right products commute.

#### Nondegenerate matrices

A bilinear map is nondegenerate when no nonzero vector is orthogonal to all vectors, on each side. For matrices the same notion is stated with the dot product.

**Definition (`Matrix.SeparatingLeft`).** An $m \times n$ matrix $M$ is separating on the left when a vector $v$ with $v \cdot (M w) = 0$ for all $w$ is $0$. The definition `Matrix.SeparatingRight` is the same on the other side.

**Definition (`Matrix.Nondegenerate`).** A matrix is nondegenerate when it is separating on the left and on the right.

The definitions hold for rectangular matrices over a semiring that is not necessarily commutative. The lemma `Matrix.separatingLeft_iff_vecMul_injective` says that $M$ is separating on the left if and only if $v \mapsto v M$ is injective, and `Matrix.separatingRight_iff_mulVec_injective` is the other side. Nondegeneracy is kept by the transpose, the conjugate transpose and a reindexing by bijections (`Matrix.nondegenerate_transpose_iff`, `Matrix.nondegenerate_conjTranspose_iff`, `Matrix.nondegenerate_submatrix_iff`). A nondegenerate matrix gives a nonzero value for each nonzero vector and some second vector (`Matrix.Nondegenerate.exists_not_ortho_of_ne_zero`).

For square matrices over a commutative ring, a determinant that is not a zero divisor gives nondegeneracy (`Matrix.Nondegenerate.of_det_mem_nonZeroDivisors`), and over a domain, a determinant that is not zero (`Matrix.Nondegenerate.of_det_ne_zero`). Over a domain the converse also holds, `Matrix.nondegenerate_iff_det_ne_zero` of the module on linear equivalences of matrices. A nondegenerate matrix sends a linearly independent family to a linearly independent family (`LinearIndependent.sum_smul_of_nondegenerate`).

The two notions of nondegeneracy correspond under the equivalences of this section.

**Theorem (`LinearMap.BilinForm.nondegenerate_iff_det_ne_zero`).** Let $B$ be a bilinear form on a module $M$ over a domain, with a finite basis $b$. Then $B$ is nondegenerate if and only if the determinant of the matrix of $B$ in $b$ is not zero.

*Proof.* The form $B$ is nondegenerate if and only if its matrix is a nondegenerate matrix (`LinearMap.BilinForm.nondegenerate_toMatrix_iff`), because the coordinates in $b$ are a linear equivalence and $B(x, y) = x \cdot (A y)$ in coordinates. Over a domain a square matrix is nondegenerate if and only if its determinant is not zero. $\square$

The general forms for bilinear maps are `LinearMap.nondegenerate_iff_det_ne_zero` and `Matrix.nondegenerate_toLinearMap₂_iff`, and the forms with one side are `LinearMap.separatingLeft_iff_det_ne_zero` and `LinearMap.separatingRight_iff_det_ne_zero`.

#### Adjoint pairs of matrices

**Definition (`Matrix.IsAdjointPair`).** For square matrices $J$ and $J'$, two matrices $A$ and $A'$ are an adjoint pair when $A^T J' = J A'$.

When $J$ and $J'$ are the matrices of bilinear forms $B$ and $B'$, this is the matrix form of the condition $B'(A x, y) = B(x, A' y)$, and `isAdjointPair_toLinearMap₂'` states this equivalence. A matrix $A$ is self adjoint for $J$ when $A^T J = J A$ (`Matrix.IsSelfAdjoint`), and skew adjoint when $A^T J = -J A$ (`Matrix.IsSkewAdjoint`). The skew adjoint matrices form a submodule, `skewAdjointMatricesSubmodule J`, with the membership rule `mem_skewAdjointMatricesSubmodule`; the self adjoint matrices are `selfAdjointMatricesSubmodule J`. For $J = 1$ the skew adjoint matrices are the matrices with $A^T = -A$, the Lie algebra of the orthogonal group; for the symplectic matrix $J$ of Chapter 10 Section 2 they are the symplectic Lie algebra. The lemma `Matrix.isAdjointPair_equiv` describes the change of $J$ by congruence with an invertible $P$.

#### Forms on quotients

A bilinear map that vanishes on submodules passes to the quotients of Chapter 1 Section 3.

**Definition (`LinearMap.liftQ₂`).** For a sesquilinear map $f : M \to N \to P$ and submodules $M' \le M$ and $N' \le N$ with $f(m', n) = 0$ for $m' \in M'$ and $f(m, n') = 0$ for $n' \in N'$, `LinearMap.liftQ₂ M' N' f hM' hN'` is the sesquilinear map $M / M' \to N / N' \to P$ with $[m], [n] \mapsto f(m, n)$.

The formula is `LinearMap.liftQ₂_mk`. For a reflexive form on one module, `LinearMap.IsRefl.liftQ₂` needs only the condition on one side. A standard use is the quotient by the kernel, which gives a nondegenerate form on $M / \ker B$.

#### Common errors

1. The matrix of a bilinear form changes as $P^T A P$, not as $P^{-1} A P$. Do not use the change of basis lemmas of linear maps of Chapter 3 Section 3 for the matrix of a form.
2. `Matrix.toLinearMap₂'` takes the ring $R$ as an explicit argument, so `Matrix.toLinearMap₂' R M`, not `Matrix.toLinearMap₂' M`. The bilinear form versions `Matrix.toBilin'` do not take it.
3. `Matrix.Nondegenerate` is a structure with two fields, not the condition on the determinant. Over a ring that is not a domain, use `Matrix.Nondegenerate.of_det_mem_nonZeroDivisors`.

### Exercises

1. (A) Compute the bilinear form `Matrix.toBilin' !![1, 2; 0, 3]` at the vectors $(1, 1)$ and $(1, -1)$ of `Fin 2 → ℚ`.
2. (A) Find the matrix of the bilinear form $B(x, y) = x_1 y_2 - x_2 y_1$ on $\mathbb{Q}^2$ in the standard basis, and check that it is nondegenerate.
3. (B) Let $b = (e_1, e_2)$ and $c = (e_1, e_1 + e_2)$ be bases of $\mathbb{Q}^2$. Compute the matrix in $c$ of the form with matrix $1$ in $b$, with `LinearMap.BilinForm.toMatrix_mul_basis_toMatrix`.
4. (B) Show that the $1 \times 2$ matrix $(1, 0)$ over $\mathbb{Q}$ is separating on the left but not on the right. Which side is separating for its transpose?
5. (B) Prove that the skew adjoint matrices for $J = 1$ have zero diagonal over a field of characteristic not $2$.
6. (C) Let $B$ be a symmetric bilinear form on $M$ and $K$ its kernel. Construct the form on $M / K$ with `LinearMap.liftQ₂`, and prove that it is nondegenerate on the left.

### Reference

<?reference?>
