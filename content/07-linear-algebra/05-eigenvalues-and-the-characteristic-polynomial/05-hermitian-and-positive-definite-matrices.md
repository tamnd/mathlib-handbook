---
title: Hermitian and positive definite matrices
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.Hermitian
  - Mathlib.LinearAlgebra.Matrix.PosDef
  - Mathlib.LinearAlgebra.Matrix.SchurComplement
  - Mathlib.LinearAlgebra.Matrix.Gershgorin
  - Mathlib.LinearAlgebra.Matrix.ZMatrix
explains:
  E2: [Matrix.IsHermitian, Matrix.IsHermitian.commute_iff, Matrix.PosSemidef, Matrix.PosDef, Matrix.posDef_iff_dotProduct_mulVec, Matrix.PosDef.det_pos, Matrix.det_fromBlocks₁₁, Matrix.det_one_add_mul_comm, eigenvalue_mem_ball, Matrix.lt_two_mul_of_mul_diagonal_posDef_of_for_le_of_hasEigen]
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

## Hermitian and positive definite matrices

### Overview

A complex matrix $A$ is Hermitian when it is equal to its conjugate transpose $A^*$ of Chapter 3 Section 7. It is positive definite when, in addition, the number $x^* A x$ is positive for each vector $x \ne 0$. These matrices are the matrices of inner products, and they are the subject of the spectral theorem of Volume 8. This section gives the algebraic part of the theory, which needs no inner product space: the definitions, the closure rules, the determinant and the trace of a positive definite matrix, and the Schur complement of a block matrix.

The section also describes two results that locate eigenvalues without a computation. The theorem of Gershgorin puts each eigenvalue in a disc around a diagonal entry. The module on Z-matrices bounds the eigenvalues of a matrix with nonpositive entries off the diagonal.

Mathlib states the definitions for matrices over a ring with a star operation and a partial order. So the same statements cover real matrices, with the trivial star, and complex matrices, with the partial order of the scope ComplexOrder.

### The library around it

#### Hermitian matrices

**Definition (`Matrix.IsHermitian`).** A square matrix $A$ over a type with a star operation is Hermitian when `A.conjTranspose = A`.

The lemma `Matrix.IsHermitian.ext_iff` gives the form with entries, $\overline{A_{ji}} = A_{ij}$, and `Matrix.IsHermitian.apply` uses it. On square matrices the conjugate transpose is the star of the matrix ring, so `Matrix.isHermitian_iff_isSelfAdjoint` identifies the Hermitian matrices with the self adjoint elements of the star ring. When the star on the entries is trivial, as for real matrices, `Matrix.isHermitian_iff_isSymm` says that Hermitian means symmetric.

The Hermitian matrices form an additive group: `Matrix.IsHermitian.add`, `Matrix.IsHermitian.sub` and `Matrix.IsHermitian.neg`. A product with a scalar is Hermitian when the scalar is self adjoint (`Matrix.IsHermitian.smul`), so the Hermitian matrices form a real vector space and not a complex one. Powers, integer powers and inverses of Hermitian matrices are Hermitian (`Matrix.IsHermitian.pow`, `Matrix.IsHermitian.zpow`, `Matrix.IsHermitian.inv`), and so is the adjugate (`Matrix.IsHermitian.adjugate`). The rule `Matrix.IsHermitian.submatrix` keeps the same rows and columns, `Matrix.IsHermitian.reindex` changes the index type, and `Matrix.IsHermitian.map` applies a map of entries that commutes with the star.

The standard examples are the matrices $A^* A$ and $A A^*$ (`Matrix.isHermitian_conjTranspose_mul_self`, `Matrix.isHermitian_mul_conjTranspose_self`) and the conjugates $B^* A B$ of a Hermitian $A$ (`Matrix.isHermitian_conjTranspose_mul_mul`). A diagonal matrix is Hermitian if and only if each diagonal entry is self adjoint (`Matrix.isHermitian_diagonal_iff`).

A product of two Hermitian matrices is not always Hermitian.

**Theorem (`Matrix.IsHermitian.commute_iff`).** Let $A$ and $B$ be Hermitian. Then $A$ and $B$ commute if and only if $A B$ is Hermitian.

*Proof.* The conjugate transpose of $A B$ is $B^* A^* = B A$. So $A B$ is Hermitian exactly when $A B = B A$. $\square$

For block matrices, `Matrix.isHermitian_fromBlocks_iff` says that the block matrix with blocks $A, B, C, D$ is Hermitian if and only if $A$ and $D$ are Hermitian and $C = B^*$. The rule `Matrix.IsHermitian.fromBlocks₁₁` reduces the condition to the Schur complement $D - B^* A^{-1} B$ when $A$ is Hermitian. The quadratic form of a Hermitian matrix takes self adjoint values, and `Matrix.IsHermitian.star_dotProduct_mulVec_comm` is the form of this fact with two vectors.

#### Positive semidefinite and positive definite matrices

The definitions use vectors of finite support, so that they also make sense for an infinite index type.

**Definition (`Matrix.PosSemidef`).** A square matrix $M$ over a ring $R$ with a partial order and a star is positive semidefinite when it is Hermitian and $0 \le \sum_{i,j} \overline{x_i} M_{ij} x_j$ for each finitely supported vector $x$.

**Definition (`Matrix.PosDef`).** The matrix $M$ is positive definite when it is Hermitian and $0 < \sum_{i,j} \overline{x_i} M_{ij} x_j$ for each finitely supported vector $x \ne 0$.

For a finite index type the conditions become the usual ones.

**Theorem (`Matrix.posDef_iff_dotProduct_mulVec`).** For a finite index type, $M$ is positive definite if and only if $M$ is Hermitian and $0 < x^* (M x)$ for each vector $x \ne 0$.

*Proof.* A vector on a finite type is the same as a finitely supported vector (the equivalence `Finsupp.equivFunOnFinite`). The finite sum $\sum_{i,j} \overline{x_i} M_{ij} x_j$ is the dot product of the star of $x$ with $M x$, by the distributive law. $\square$

The semidefinite version is `Matrix.posSemidef_iff_dotProduct_mulVec`. A positive definite matrix is positive semidefinite (`Matrix.PosDef.posSemidef`). The sum of two positive definite matrices is positive definite (`Matrix.PosDef.add`), and so is a positive multiple (`Matrix.PosDef.smul`). The positive semidefinite matrices form an additive submonoid, `Matrix.PosSemidef.addSubmonoid`. The matrices $A^* A$ are positive semidefinite (`Matrix.posSemidef_conjTranspose_mul_self`), and positive definite when $x \mapsto A x$ is injective (`Matrix.PosDef.conjTranspose_mul_self`). The conjugate $B^* M B$ of a positive definite $M$ is positive definite when $B$ is injective on vectors (`Matrix.PosDef.conjTranspose_mul_mul_same`).

The diagonal entries of a positive definite matrix are positive (`Matrix.PosDef.diag_pos`), so the trace is positive when the index type is not empty (`Matrix.PosDef.trace_pos`). A principal submatrix of a positive definite matrix is positive definite (`Matrix.PosDef.submatrix`, for an injective map of indices), and `Matrix.posDef_iff_submatrix_finset` says that a matrix is positive definite if and only if each finite principal submatrix is.

**Theorem (`Matrix.PosDef.det_pos`).** Over a nontrivial ordered commutative ring with a star, the determinant of a positive definite matrix is positive.

*Proof sketch.* Reindex by `Fin k` and use induction on $k$. Let $N$ be positive definite of size $k + 1$ and let $M$ be the submatrix without the first row and column. Then $M$ is positive definite, so $\det M > 0$ by induction. Let $v$ be the first column of the adjugate of $N$. Its first entry is $\det M$, so $v \ne 0$, and $N v = \det N \cdot e_0$. Then $0 < v^* N v = \det N \cdot \overline{v_0} = \det N \det M$, since $\det M$ is self adjoint. As $\det M > 0$, also $\det N > 0$. $\square$

A positive definite matrix is invertible (`Matrix.PosDef.isUnit`), and its inverse is positive definite (`Matrix.PosDef.inv`). Over a field, a positive semidefinite matrix is positive definite if and only if it is a unit (`Matrix.PosSemidef.posDef_iff_isUnit`), and `Matrix.PosSemidef.posDef_iff_det_ne_zero` is the same statement with the determinant. A diagonal matrix is positive definite if and only if its diagonal entries are positive (`Matrix.posDef_diagonal_iff`).

The matrix of a quadratic form in a basis is positive definite if and only if the form is positive definite, `QuadraticForm.posDef_toMatrix'`. The Cauchy and Schwarz inequality $|x^* A y|^2 \le (x^* A x)(y^* A y)$ for a positive definite matrix $A$ is `Matrix.PosDef.star_dotProduct_mulVec_mul_le`. For an integer valued positive definite form, `Matrix.PosDef.finite_setOfPred_dotProduct_mulVec_le` says that only finitely many integer vectors have a value at most a given bound; this is the start of the reduction theory of quadratic forms in the volumes on number theory. The analytic results, such as the square root of a positive semidefinite matrix and the eigenvalue criterion, need the spectral theorem and are in Volume 8.

#### The Schur complement

For a block matrix $\begin{pmatrix} A & B \\ C & D \end{pmatrix}$ with an invertible block $A$, the matrix $D - C A^{-1} B$ is the Schur complement of $A$. It comes from block elimination: `Matrix.fromBlocks_eq_of_invertible₁₁` writes the block matrix as a product of a lower triangular block matrix, a block diagonal matrix with the blocks $A$ and $D - C A^{-1} B$, and an upper triangular block matrix.

**Theorem (`Matrix.det_fromBlocks₁₁`).** If $A$ is invertible, then $\det \begin{pmatrix} A & B \\ C & D \end{pmatrix} = \det A \cdot \det(D - C A^{-1} B)$.

*Proof.* Take the determinant of the factorization above. The two triangular factors have identity blocks on the diagonal, so their determinants are $1$ (Chapter 4 Section 1). The determinant of the block diagonal factor is the product of the determinants of the blocks. $\square$

The version with an invertible $D$ is `Matrix.det_fromBlocks₂₂`, and `Matrix.det_fromBlocks_one₁₁` is the case $A = 1$. The inverse of a block triangular matrix is `Matrix.invOf_fromBlocks_zero₂₁_eq`, and `Matrix.isUnit_fromBlocks_zero₂₁` says when it is a unit. The instance `Matrix.fromBlocks₁₁Invertible` builds an inverse of the block matrix from inverses of $A$ and of the Schur complement, with the formula `Matrix.invOf_fromBlocks₁₁_eq`.

The determinant formula gives an identity for rectangular matrices.

**Theorem (`Matrix.det_one_add_mul_comm`).** For an $m \times n$ matrix $A$ and an $n \times m$ matrix $B$ over a commutative ring, $\det(1 + A B) = \det(1 + B A)$.

*Proof.* Compute the determinant of $\begin{pmatrix} 1 & -A \\ B & 1 \end{pmatrix}$ in two ways. With the Schur complement of the upper left block, it is $\det(1 + B A)$. With the Schur complement of the lower right block, it is $\det(1 + A B)$. $\square$

This is the identity of Weinstein and Aronszajn, also called Sylvester's determinant identity. The variants are `Matrix.det_mul_add_one_comm` and `Matrix.det_one_sub_mul_comm`. With $n = 1$ it gives `Matrix.det_one_add_replicateCol_mul_replicateRow`: $\det(1 + u v^T) = 1 + v \cdot u$. The general form `Matrix.det_add_mul` is the matrix determinant lemma, $\det(A + U V) = \det A \det(1 + V A^{-1} U)$ for $A$ with a unit determinant.

For Hermitian blocks, the Schur complement decides the positivity. `Matrix.PosDef.fromBlocks₁₁` says that, for a positive definite $A$, the block matrix with blocks $A, B, B^*, D$ is positive semidefinite if and only if $D - B^* A^{-1} B$ is. The proof uses the identity `Matrix.schur_complement_eq₁₁`, which writes the quadratic form of the block matrix as a sum of a form in $A$ and a form in the Schur complement.

#### Location of eigenvalues

**Theorem (`eigenvalue_mem_ball`).** Let $A$ be a square matrix over a normed field and $\mu$ an eigenvalue of `Matrix.toLin' A`. Then there is an index $k$ with $\|\mu - A_{kk}\| \le \sum_{j \ne k} \|A_{kj}\|$.

*Proof.* Let $v$ be an eigenvector and $k$ an index where $\|v_k\|$ is a maximum, so $v_k \ne 0$. Row $k$ of $A v = \mu v$ gives $(\mu - A_{kk}) v_k = \sum_{j \ne k} A_{kj} v_j$. Take norms and divide by $\|v_k\|$, with $\|v_j\| \le \|v_k\|$. $\square$

So each eigenvalue is in one of the discs of Gershgorin. A matrix is strictly diagonally dominant when $\sum_{j \ne k} \|A_{kj}\| < \|A_{kk}\|$ for each $k$. Then $0$ is in no disc, so $0$ is not an eigenvalue, and `det_ne_zero_of_sum_row_lt_diag` says that $\det A \ne 0$. The version for columns is `det_ne_zero_of_sum_col_lt_diag`.

A Z-matrix is a real matrix with $A_{ij} \le 0$ for $i \ne j$. The module `Mathlib.LinearAlgebra.Matrix.ZMatrix` studies such matrices when $D A$ is positive definite for a diagonal matrix $D$ with positive entries. The Cartan matrices of Chapter 6 Section 4 are the main examples. First, `Matrix.diag_pos_of_mul_diagonal_posDef` says that the diagonal entries of $A$ are then positive.

**Theorem (`Matrix.lt_two_mul_of_mul_diagonal_posDef_of_for_le_of_hasEigen`).** Over a linearly ordered commutative ring with the trivial star, such as $\mathbb{R}$, let $d$ be a vector with positive entries such that $\operatorname{diag}(d) A$ is positive definite. If $A_{ij} \le 0$ for $i \ne j$, $A_{ii} \le \mu$ for each $i$, and $\rho$ is an eigenvalue of `Matrix.toLin' A`, then $\rho < 2 \mu$.

For a Cartan matrix, with $2$ on the diagonal, this says that each eigenvalue is less than $4$.

#### Common errors

1. Complex numbers have no order by default. To use `Matrix.PosDef` for complex matrices, write `open ComplexOrder`; without it, the instance of a partial order on ℂ is not found.
2. `Matrix.PosDef` includes the condition `Matrix.IsHermitian`. A real matrix with $x^T A x > 0$ for all $x \ne 0$ that is not symmetric, such as `!![1, 1; -1, 1]`, is not positive definite in Mathlib.
3. `Matrix.IsHermitian.smul` needs a self adjoint scalar. The product of a Hermitian matrix with the complex number $i$ is not Hermitian.

### Exercises

1. (A) Show that `!![2, Complex.I; -Complex.I, 2]` is Hermitian.
2. (A) Prove that a diagonal real matrix with positive diagonal entries is positive definite, with `Matrix.posDef_diagonal_iff`.
3. (B) Prove that the real matrix `!![2, -1; -1, 2]` is positive definite, and compute its determinant with `Matrix.det_fin_two`.
4. (B) Prove from `Matrix.det_one_add_mul_comm` that $A B$ and $B A$ have the same nonzero eigenvalues for square matrices over a field.
5. (B) Use `det_ne_zero_of_sum_row_lt_diag` to show that the $3 \times 3$ real matrix with $4$ on the diagonal and $1$ elsewhere is invertible.
6. (C) Let $A$ be positive definite and $B$ a square matrix of the same size. Prove that the block matrix with blocks $A, B, B^*, B^* A^{-1} B$ is positive semidefinite, with `Matrix.PosDef.fromBlocks₁₁`.

### Reference

<?reference?>
