---
title: Conjugate transpose, symmetric and diagonal matrices
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.ConjTranspose
  - Mathlib.LinearAlgebra.Matrix.Symmetric
  - Mathlib.LinearAlgebra.Matrix.IsDiag
  - Mathlib.LinearAlgebra.Matrix.Orthogonal
explains:
  E2: [Matrix.conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_list_prod, Matrix.star_eq_conjTranspose, Matrix.IsSymm, Matrix.isSymm_fromBlocks_iff, Matrix.IsSymm.dotProduct_mulVec_comm, Matrix.IsDiag, Matrix.IsDiag.diagonal_diag, Matrix.HasOrthogonalRows]
  E1: auto
families: []
requires: [V02, V03, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Conjugate transpose, symmetric and diagonal matrices

### Overview

Over the complex numbers, the transpose of Section 1 is not the right operation for inner products: the adjoint of a matrix is its transpose with each entry conjugated. Mathlib defines this conjugate transpose for matrices over any type with a star operation, so that it covers the complex case, the quaternions and the plain transpose over a commutative ring with the trivial star at the same time.

This section also describes three classes of square matrices defined by a simple condition on the entries: symmetric matrices with $A^T = A$, diagonal matrices with zero entries off the diagonal, and matrices with orthogonal rows or columns. Hermitian matrices, the matrices with $A^* = A$, are in Chapter 5 with positive definite matrices.

### The library around it

#### The conjugate transpose

**Definition (`Matrix.conjTranspose`).** For a matrix $M$ with entries in a type with a star operation, `Matrix.conjTranspose M` is the matrix with the entry $\overline{M_{ij}}$ at $(j, i)$. The postfix notation for it is ᴴ.

The lemma `Matrix.conjTranspose_apply` states the definition entry by entry. The operation is an involution (`Matrix.conjTranspose_conjTranspose`), it is injective (`Matrix.conjTranspose_injective`), and it commutes with sums and differences (`Matrix.conjTranspose_add`, `Matrix.conjTranspose_sub`, `Matrix.conjTranspose_sum`). For a scalar $c$, `Matrix.conjTranspose_smul` says $(c M)^* = \bar c M^*$. Natural numbers, integers and rationals have the trivial star, so `Matrix.conjTranspose_natCast_smul` and the other cast lemmas have no conjugate. When the star on the entries is trivial, as for real matrices, `Matrix.conjTranspose_eq_transpose_of_trivial` says that the conjugate transpose is the transpose.

**Theorem (`Matrix.conjTranspose_mul`).** Over a semiring with a star operation that reverses products, $(M N)^* = N^* M^*$.

*Proof.* The entry $(k, i)$ of $(M N)^*$ is $\overline{\sum_j M_{ij} N_{jk}} = \sum_j \overline{N_{jk}}\, \overline{M_{ij}}$, because the star is additive and $\overline{a b} = \bar b \bar a$. This is the entry $(k, i)$ of $N^* M^*$. $\square$

The order of the factors in $\bar b \bar a$ is the reason why the statement holds for noncommutative entries such as quaternions. For a list of matrices, `Matrix.conjTranspose_list_prod` gives the product of the conjugate transposes in the reverse order, and `Matrix.conjTranspose_pow` is the case of powers.

On square matrices the conjugate transpose is the star operation of the matrix ring.

**Theorem (`Matrix.star_eq_conjTranspose`).** For square matrices, `star M = M.conjTranspose`.

The instance `Matrix.instStarRing` makes the square matrices a star ring, and `Matrix.instStarModule` makes them a star module. So the results of the volumes on star algebras apply to matrices: self adjoint elements, unitary elements and the real and imaginary parts of Chapter 2 Section 6. The structured forms of the operation are `Matrix.conjTransposeAddEquiv` and `Matrix.conjTransposeLinearEquiv`, and on square matrices `Matrix.conjTransposeRingEquiv` and `Matrix.conjTransposeAlgEquiv`, which take values in the opposite ring because the operation reverses products.

The interaction with vectors is in the lemmas `Matrix.star_mulVec`, `Matrix.star_vecMul`, `Matrix.mulVec_conjTranspose` and `Matrix.vecMul_conjTranspose`. For example `Matrix.star_mulVec` says that the conjugate of $M v$ is the row vector $\bar v M^*$. The lemmas `Matrix.conjTranspose_submatrix`, `Matrix.conjTranspose_reindex` and `Matrix.conjTranspose_single` describe the conjugate transpose of the constructions of Sections 5 and 6, and `Matrix.diagonal_conjTranspose` that of a diagonal matrix. The lemma `Matrix.conjTranspose_transpose` says that $(M^*)^T$ is the entrywise conjugate `M.map star`.

#### Symmetric matrices

**Definition (`Matrix.IsSymm`).** A square matrix $A$ is symmetric, `Matrix.IsSymm A`, when `A.transpose = A`.

The lemma `Matrix.IsSymm.ext_iff` gives the form with entries, $A_{ji} = A_{ij}$ for all $i, j$, and `Matrix.IsSymm.apply` uses it. The symmetric matrices are closed under the module operations (`Matrix.IsSymm.add`, `Matrix.IsSymm.smul`, `Matrix.IsSymm.neg`), under powers (`Matrix.IsSymm.pow`), under entrywise maps (`Matrix.IsSymm.map`) and under the restriction to the same rows and columns (`Matrix.IsSymm.submatrix`). They are not closed under products: $A B$ is symmetric only when $A$ and $B$ commute. The standard examples are `Matrix.isSymm_one`, `Matrix.isSymm_diagonal`, `Matrix.isSymm_transpose_mul_self` and `Matrix.isSymm_add_transpose_self`, which say that $1$, a diagonal matrix, $A^T A$ and $A + A^T$ are symmetric.

**Theorem (`Matrix.isSymm_fromBlocks_iff`).** The block matrix with blocks $A, B, C, D$ is symmetric if and only if $A$ and $D$ are symmetric and $B^T = C$.

*Proof.* The transpose of the block matrix is the block matrix with blocks $A^T, C^T, B^T, D^T$ (Section 5). Two block matrices are equal when their four blocks are equal. So the condition is $A^T = A$, $C^T = B$, $B^T = C$ and $D^T = D$, and the two middle conditions are equivalent. $\square$

The library states the middle conditions separately, and `Matrix.IsSymm.fromBlocks` is the direction that builds a symmetric block matrix. A symmetric matrix gives a symmetric bilinear form, which is the link with Chapter 6.

**Theorem (`Matrix.IsSymm.dotProduct_mulVec_comm`).** Over a commutative semiring, if $A$ is symmetric, then $x \cdot A y = y \cdot A x$ for all vectors $x$ and $y$.

*Proof.* The left side is $\sum_{i,j} x_i A_{ij} y_j$ and the right side is $\sum_{i,j} y_i A_{ij} x_j$. Exchange the names of $i$ and $j$ in the second sum and use $A_{ji} = A_{ij}$ and the commutativity of the product. $\square$

For a block matrix built from a matrix of matrices, `Matrix.isSymm_comp_iff` gives the condition on the blocks. The predicate is decidable when the equality of matrices is decidable (`Matrix.instDecidableIsSymmOfEqTranspose`), so the decide tactic checks it for a concrete matrix over a type with decidable equality.

#### Diagonal matrices

The matrix `Matrix.diagonal d` of Section 1 is built from a vector. The predicate below says that a given matrix has this form.

**Definition (`Matrix.IsDiag`).** A square matrix $A$ is diagonal, `Matrix.IsDiag A`, when $A_{ij} = 0$ for all $i \ne j$.

**Theorem (`Matrix.IsDiag.diagonal_diag`).** If $A$ is diagonal, then `Matrix.diagonal A.diag = A`.

*Proof.* The two matrices agree on the diagonal, where both entries are $A_{ii}$. Off the diagonal the entry of `Matrix.diagonal A.diag` is $0$ by definition, and the entry of $A$ is $0$ by hypothesis. $\square$

The equivalence `Matrix.isDiag_iff_diagonal_diag` states both directions, and `Matrix.isDiag_diagonal` is the converse. The closure lemmas are `Matrix.IsDiag.add`, `Matrix.IsDiag.smul`, `Matrix.IsDiag.transpose`, `Matrix.IsDiag.conjTranspose` and `Matrix.IsDiag.kronecker`, the last for the Kronecker product of Section 8. A diagonal matrix is symmetric (`Matrix.IsDiag.isSymm`). For block matrices, `Matrix.isDiag_fromBlocks_iff` says that the block matrix is diagonal if and only if $A$ and $D$ are diagonal and $B = 0$ and $C = 0$. The lemma `Matrix.IsDiag.submatrix` needs an injective map of indices, because a map that sends two indices to the same index can move a diagonal entry off the diagonal.

#### Orthogonal rows and columns

**Definition (`Matrix.HasOrthogonalRows`).** A matrix $A$ has orthogonal rows when the dot product of two different rows is $0$.

The predicate `Matrix.HasOrthogonalCols` is the same for columns. The dot product here is the plain dot product, without a conjugate, so for complex matrices this is not orthogonality for the usual inner product. The two notions exchange under the transpose: `Matrix.transpose_hasOrthogonalCols_iff_hasOrthogonalRows`. The link with the class of diagonal matrices is the main result of the module `Mathlib.LinearAlgebra.Matrix.Orthogonal`: `Matrix.mul_transpose_self_isDiag_iff_hasOrthogonalRows` says that $A A^T$ is diagonal if and only if $A$ has orthogonal rows, since the entry $(i, j)$ of $A A^T$ is the dot product of the rows $i$ and $j$. The lemma `Matrix.transpose_mul_self_isDiag_iff_hasOrthogonalCols` is the version for columns. The orthogonal group, the matrices with $A A^T = 1$, is in Chapter 10.

#### Common errors

1. Over the real numbers $M^*$ and $M^T$ are equal, but not by definition. Use `Matrix.conjTranspose_eq_transpose_of_trivial` to change one into the other.
2. `Matrix.IsSymm` is about the transpose, also for complex matrices. The condition $A^* = A$ is `Matrix.IsHermitian` of Chapter 5.
3. `Matrix.IsDiag A` is a property of a matrix, and `Matrix.diagonal d` is a matrix. To use a lemma about `Matrix.diagonal` for a matrix with `Matrix.IsDiag A`, first rewrite $A$ with `Matrix.IsDiag.diagonal_diag`.

### Exercises

1. (A) Compute the conjugate transpose of `!![1, Complex.I; 2, 3 + Complex.I]`.
2. (A) Prove that $A^T A$ is symmetric for each matrix $A$ over a commutative ring, from `Matrix.transpose_mul`.
3. (B) Prove that the product of two symmetric matrices is symmetric if and only if the two matrices commute.
4. (B) Prove that a matrix that is symmetric and upper triangular is diagonal.
5. (B) Show that `!![1, 1; 1, -1]` has orthogonal rows, and compute $A A^T$.
6. (C) Prove that $M^* M = 0$ implies $M = 0$ for complex matrices, with `Matrix.conjTranspose_mul_self_eq_zero` of Section 6, and give a $2 \times 2$ complex matrix $M \ne 0$ with $M^T M = 0$.

### Reference

<?reference?>
