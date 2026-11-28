---
title: Matrix norms and positive matrices
kind: api
modules:
  - Mathlib.Analysis.Matrix.Normed
  - Mathlib.Analysis.Normed.Lp.Matrix
  - Mathlib.Analysis.Matrix.Hermitian
  - Mathlib.Analysis.Matrix.Spectrum
  - Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
  - Mathlib.Analysis.Matrix.PosDef
  - Mathlib.Analysis.Matrix.Order
  - Mathlib.Analysis.Matrix.LDL
  - Mathlib.Analysis.Matrix.MeasurableSpace
explains:
  E2: [Matrix.linftyOpNormedRing, Matrix.frobeniusNormedRing, Matrix.norm_le_iff, Matrix.toLpLin, Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.spectral_theorem, Matrix.IsHermitian.posDef_iff_eigenvalues_pos, Matrix.nonneg_iff_posSemidef, Matrix.PosSemidef.hadamard, LDL.lower_conj_diag]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Matrix norms and positive matrices

### Overview

A matrix with entries in a normed field is a vector in a finite dimensional space, so all norms on the matrices give the same topology. The norms are different as numbers, and each one has its own use. The largest entry is simple to compute. The Frobenius norm comes from an inner product. The operator norms make the matrices a normed ring, so that $\|A B\| \le \|A\| \|B\|$. Mathlib does not choose one norm for `Matrix m n α`. It gives each norm as a definition that you turn on with a scoped instance.

The second half of the section treats Hermitian and positive matrices over $\mathbb{R}$ or $\mathbb{C}$. A Hermitian matrix has real eigenvalues and an orthonormal basis of eigenvectors, by the spectral theorem of section 3. A positive semidefinite matrix is a Hermitian matrix with eigenvalues at least $0$. The positive semidefinite matrices give a partial order on the square matrices, a continuous functional calculus, and the decomposition $S = L D L^*$ of a positive definite matrix.

### The library around it

The module `Mathlib.Analysis.Matrix.Normed` gives three norms. With `open scoped Matrix.Norms.Elementwise`, the norm of $A$ is the largest norm of an entry, and the instance is `Matrix.normedAddCommGroup`. The lemma `Matrix.norm_le_iff` states that $\|A\| \le r$ if and only if $\|A_{ij}\| \le r$ for all $i$ and $j$, when $r \ge 0$. The lemma `Matrix.norm_apply_le_norm` bounds each entry. This norm is not submultiplicative, so it gives no normed ring.

With `open scoped Matrix.Norms.Operator`, the norm of $A$ is the largest sum $\sum_j \|A_{ij}\|$ over the rows, as `Matrix.linfty_opNorm_def` states. This is the operator norm of $A$ on the space of functions $n \to \alpha$ with the sup norm, by `Matrix.linfty_opNorm_eq_opNorm`. The definition `Matrix.linftyOpNormedRing` makes the square matrices a normed ring, and `Matrix.linfty_opNorm_mul` and `Matrix.linfty_opNorm_mulVec` give the two submultiplicative bounds. The lemma `Matrix.linfty_opNorm_toMatrix` states that the matrix of a continuous linear map has the same norm as the map.

With `open scoped Matrix.Norms.Frobenius`, the norm of $A$ is $(\sum_{i,j} \|A_{ij}\|^2)^{1/2}$, by `Matrix.frobenius_norm_def`. Over $\mathbb{R}$ or $\mathbb{C}$ this norm is submultiplicative, by `Matrix.frobenius_norm_mul`, and `Matrix.frobeniusNormedRing` is the normed ring. The Frobenius norm of the identity is $\sqrt{n}$ and not $1$, so this ring is not a `NormOneClass`. The lemmas `Matrix.frobenius_norm_transpose` and `Matrix.frobenius_norm_conjTranspose` state that the norm does not change under the transpose and the conjugate transpose. The operator norm for the Euclidean norm on vectors is the $C^*$ norm of the matrices, and it is in the volume on $C^*$ algebras.

The module `Mathlib.Analysis.Normed.Lp.Matrix` links matrices and the spaces $\ell^p$ of chapter 1. The map `Matrix.toLpLin p q` sends a matrix to the linear map from `WithLp p (n → R)` to `WithLp q (m → R)` that multiplies by the matrix. The lemmas `Matrix.toLpLin_mul`, `Matrix.toLpLin_one` and `Matrix.toLpLin_pow` state that it respects products. The lemma `LinearMap.det_toLpLin` states that the determinant does not change. The lemma `Matrix.spectrum_toLpLin` states that the spectrum of the matrix and of the linear map are equal.

The predicate `Matrix.IsHermitian` is in linear algebra. The analytic results begin with `Matrix.isSymmetric_toEuclideanLin_iff`: a matrix is Hermitian if and only if its map on the Euclidean space `EuclideanSpace 𝕜 n` is symmetric. Thus the spectral theorem for symmetric operators applies. For a Hermitian matrix $A$, the function `Matrix.IsHermitian.eigenvalues` gives the real eigenvalues $\lambda_i$ of $A$, and `Matrix.IsHermitian.eigenvectorBasis` gives an orthonormal basis of eigenvectors. The lemma `Matrix.IsHermitian.mulVec_eigenvectorBasis` states that each basis vector is an eigenvector. The unitary matrix `Matrix.IsHermitian.eigenvectorUnitary` has these vectors as columns. The lemma `Matrix.IsHermitian.spectral_theorem` states that $A = U D U^*$, where $D$ is the diagonal matrix of eigenvalues. The consequences are `Matrix.IsHermitian.det_eq_prod_eigenvalues`, `Matrix.IsHermitian.trace_eq_sum_eigenvalues`, `Matrix.IsHermitian.charpoly_eq` and `Matrix.IsHermitian.rank_eq_card_non_zero_eigs`. The function `Matrix.IsHermitian.eigenvalues₀` lists the eigenvalues in decreasing order, and `Matrix.IsHermitian.eigenvalues₀_antitone` states this order.

The module `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus` uses the spectral theorem to apply a continuous function $f : \mathbb{R} \to \mathbb{R}$ to a Hermitian matrix. The matrix `Matrix.IsHermitian.cfc` of $f$ is $f(A) = U \operatorname{diag}(f(\lambda_i)) U^*$, with $U$ and $\lambda_i$ from the spectral theorem. For example, $f(x) = x^2$ gives $A^2$, and $f(x) = \max(x, 0)$ gives the positive part of $A$. The instance `Matrix.IsHermitian.instContinuousFunctionalCalculus` connects this to the general functional calculus `cfc`, and `Matrix.IsHermitian.cfc_eq` states that the two agree. So the square root `CFC.sqrt` and the absolute value `CFC.abs` of the general theory apply to matrices.

The predicates `Matrix.PosSemidef` and `Matrix.PosDef` are in linear algebra. The module `Mathlib.Analysis.Matrix.PosDef` describes them by eigenvalues. The lemma `Matrix.IsHermitian.posDef_iff_eigenvalues_pos` states that a Hermitian matrix is positive definite if and only if all its eigenvalues are positive, and `Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg` is the semidefinite form. The lemma `Matrix.PosSemidef.det_nonneg` follows, and `Matrix.PosSemidef.trace_eq_zero_iff` states that the trace is zero only for the zero matrix. A positive semidefinite matrix $M$ gives the inner product $\langle x, y \rangle = y^* M x$ on vectors, by `Matrix.toInnerProductSpace`.

The module `Mathlib.Analysis.Matrix.Order` defines the Loewner order: $A \le B$ when $B - A$ is positive semidefinite, by `Matrix.le_iff`. The order is scoped, so use `open scoped MatrixOrder`. The lemma `Matrix.nonneg_iff_posSemidef` states that $0 \le A$ if and only if $A$ is positive semidefinite, and `Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg` gives the form with the spectrum. The instance `Matrix.instStarOrderedRing` states that the nonnegative matrices are the matrices of the form $B^* B$. The theorem of Schur is `Matrix.PosSemidef.hadamard`: the entrywise product of two positive semidefinite matrices is positive semidefinite. The lemmas `Matrix.PosDef.hadamard` and `Matrix.PosDef.kronecker` give the positive definite form and the Kronecker product.

The module `Mathlib.Analysis.Matrix.LDL` decomposes a positive definite matrix $S$ on an ordered index type. The matrix `LDL.lower` is lower triangular, by `LDL.isLowerTriangular_lower`, and `LDL.diag` is diagonal. The lemma `LDL.lower_conj_diag` states that $S = L D L^*$. The proof applies the Gram-Schmidt process to the standard basis for the inner product of $S$, as `LDL.lowerInv_eq_gramSchmidtBasis` states. Last, `Mathlib.Analysis.Matrix.MeasurableSpace` gives the matrices the product measurable space. The lemma `Matrix.measurable_iff` states that a map into matrices is measurable if and only if each entry is measurable.

#### Common errors

1. Writing `‖A‖` for a matrix with no scoped instance open. Mathlib has no global norm on matrices. Write `open scoped Matrix.Norms.Elementwise`, `open scoped Matrix.Norms.Frobenius` or `open scoped Matrix.Norms.Operator`, and use the lemmas with the matching prefix, such as `Matrix.linfty_opNorm_mul` for the operator norm.
2. Expecting `Matrix.norm_le_iff` to hold for all $r$. It needs $0 \le r$, since for $r < 0$ the right side is true for an empty matrix and the left side is false. The strict form `Matrix.norm_lt_iff` needs $0 < r$.
3. Using $A \le B$ for matrices without `open scoped MatrixOrder`. Without it, Lean finds no order instance. The Loewner order is not the entrywise order.

### Exercises

1. (A) With the elementwise norm, let $J$ be the $2 \times 2$ matrix of ones. Show that $\|J^2\| > \|J\|^2$, so the elementwise norm is not submultiplicative.
2. (A) Use `Matrix.linfty_opNorm_diagonal` to compute the operator norm of $\operatorname{diag}(1, -3, 2)$.
3. (B) Show that the matrix with rows $(2, 1)$ and $(1, 2)$ is positive definite, first with `Matrix.IsHermitian.posDef_iff_eigenvalues_pos` and then from the definition.
4. (B) Prove from `Matrix.IsHermitian.spectral_theorem` that the trace of a Hermitian matrix is the sum of its eigenvalues.
5. (B) Show that $A \le B$ in the Loewner order implies $\operatorname{tr} A \le \operatorname{tr} B$, with `Matrix.tracePositiveLinearMap`.
6. (C) Prove the theorem of Schur, `Matrix.PosSemidef.hadamard`, by writing each matrix as a sum of matrices $v v^*$ and computing the entrywise product of two such matrices.

### Reference

<?reference?>
