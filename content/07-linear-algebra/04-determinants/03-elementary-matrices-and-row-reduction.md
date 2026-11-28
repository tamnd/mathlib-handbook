---
title: Elementary matrices, transvections and row reduction
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.Permutation
  - Mathlib.LinearAlgebra.Matrix.Swap
  - Mathlib.LinearAlgebra.Matrix.Transvection
  - Mathlib.LinearAlgebra.Transvection.Basic
  - Mathlib.LinearAlgebra.Transvection.Generation
  - Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
  - Mathlib.LinearAlgebra.Matrix.Echelon.Basic
  - Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition
  - Mathlib.LinearAlgebra.Matrix.Echelon.Pivot
  - Mathlib.LinearAlgebra.Center
  - Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
  - Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
  - Mathlib.LinearAlgebra.Matrix.Determinant.Misc
  - Mathlib.LinearAlgebra.Matrix.AbsoluteValue
  - Mathlib.LinearAlgebra.Matrix.Polynomial
  - Mathlib.LinearAlgebra.Matrix.MvPolynomial
  - Mathlib.LinearAlgebra.FreeModule.Determinant
explains:
  E2: [Equiv.Perm.permMatrix, Matrix.rowScale, Matrix.transvection, Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec, Matrix.diagonal_transvection_induction_of_det_ne_zero, Matrix.RowEquivalent, Matrix.IsRowEchelon, Echelon.Decomposition, LinearMap.transvection, LinearEquiv.mem_transvections_pow_mul_dilatransvections_of_not_isExceptional]
  E1: auto
families: []
requires: [V03, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Elementary matrices, transvections and row reduction

### Overview

Gaussian elimination reduces a matrix with three kinds of row operations: exchange two rows, multiply a row by a unit, and add a multiple of one row to another. Each operation is the product on the left with an elementary matrix. Over a field, the elimination shows that each matrix is a product of elementary matrices and a diagonal matrix, and it computes the rank and the determinant.

Mathlib has each part of this theory. The permutation matrices and the swap matrices give the exchanges, `Matrix.rowScale` gives the scaling, and `Matrix.transvection` gives the addition of a multiple of a row. The reduction to a diagonal matrix is a theorem over fields, and it gives a principle of induction for matrices. The echelon forms and the echelon decompositions give the rank and the determinant from a certificate. In the basis free form, a transvection is a linear map $x \mapsto x + f(x) v$, and the theorem of Dieudonné writes a linear automorphism as a short product of such maps.

### The library around it

#### Permutation and swap matrices

**Definition (`Equiv.Perm.permMatrix`).** For a permutation $\sigma$ of $n$, `Equiv.Perm.permMatrix R σ` is the matrix of $\sigma$ as a partial equivalence of Chapter 3 Section 4, with the entry $1$ at $(i, \sigma(i))$ and $0$ elsewhere.

The product with a vector permutes its entries: `Matrix.permMatrix_mulVec` says $P_\sigma v = v \circ \sigma$, and `Matrix.vecMul_permMatrix` gives the row version. The map $\sigma \mapsto P_\sigma$ reverses products (`Matrix.permMatrix_mul`), and the transpose of $P_\sigma$ is $P_{\sigma^{-1}}$ (`Matrix.transpose_permMatrix`). The trace counts the fixed points (`Matrix.trace_permutation`).

**Theorem (`Matrix.det_permutation`).** Over a commutative ring, $\det P_\sigma = \operatorname{sign}(\sigma)$.

*Proof.* In the formula of Leibniz of Section 1, the only permutation $\tau$ with all entries $(P_\sigma)_{i, \tau(i)}$ nonzero is $\tau = \sigma$, and the product of these entries is $1$. So the determinant is $\operatorname{sign}(\sigma)$. $\square$

The exchange of two rows is the case of a transposition: `Matrix.swap R i j` is the permutation matrix of `Equiv.swap i j`. The lemmas `Matrix.swap_mulVec`, `Matrix.swap_mul_self`, `Matrix.transpose_swap` and `Matrix.isSymm_swap` give its main properties, and `Matrix.swap_mul_of_ne` says that the product $S_{ij} M$ keeps the rows other than $i$ and $j$. The element of the general linear group is `Matrix.GeneralLinearGroup.swap`.

#### Scaling and transvections

**Definition (`Matrix.rowScale`).** For an index $i$ and a scalar $c$, `Matrix.rowScale i c` is the diagonal matrix with the entry $c$ at $i$ and $1$ elsewhere.

By `Matrix.rowScale_mul`, the product on the left multiplies the row $i$ by $c$, and `Matrix.mul_rowScale` is the version for columns. The lemma `Matrix.rowScale_mul_rowScale` multiplies the scalars, and for a unit $c$ the matrix is the element `Matrix.GeneralLinearGroup.rowScale` of the general linear group.

**Definition (`Matrix.transvection`).** For indices $i \ne j$ and a scalar $c$, `Matrix.transvection i j c` is the matrix $1 + c E_{ij}$, with the matrix unit $E_{ij}$ of Chapter 3.

The product $T_{ij}(c) M$ adds $c$ times the row $j$ to the row $i$; `Matrix.updateRow_eq_transvection` states that the matrix is the identity with the row $i$ replaced by $e_i + c e_j$. The rules are `Matrix.transvection_zero`, `Matrix.transvection_mul_transvection_same` (the scalars add) and `Matrix.det_transvection_of_ne` (the determinant is $1$). The structure `Matrix.TransvectionStruct` bundles the data $i$, $j$, the proof of $i \ne j$ and $c$, so that a list of transvections is a list of elements of one type; its matrix is `Matrix.TransvectionStruct.toMatrix`, and `Matrix.TransvectionStruct.det_toMatrix_prod` says that a product of transvections has determinant $1$.

#### Reduction to a diagonal matrix

**Theorem (`Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`).** Over a field, each square matrix $M$ indexed by a finite type with a linear order can be written $M = L D L'$, where $L$ and $L'$ are products of transvections and $D$ is diagonal.

*Proof sketch.* The proof is by induction on the size, with the index type `Fin r ⊕ Unit`. If the last column or the last row has a nonzero entry, transvections move a nonzero entry to the corner, and then clear the rest of the last row and column. If the last row and column are zero, nothing is to be done. The block that remains has size $r$, and the induction applies to it. The equivalent form `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal` says that $L M L'$ is diagonal. $\square$

The transvections have determinant $1$, so $\det M = \det D$. The theorem gives a principle of induction.

**Theorem (`Matrix.diagonal_transvection_induction_of_det_ne_zero`).** Let $P$ be a property of the square matrices over a field. If $P$ holds for the invertible diagonal matrices and the transvections, and if $P(A)$ and $P(B)$ imply $P(A B)$ for invertible $A$ and $B$, then $P$ holds for each invertible matrix.

The variant `Matrix.diagonal_transvection_induction` asks $P$ for the diagonal matrices with the same determinant as the given matrix. Mathlib uses this principle in measure theory, to prove that the linear map of $M$ scales the Lebesgue measure by $|\det M|$. The module `Mathlib.LinearAlgebra.Matrix.Transvection` also shows that the matrices that commute with all transvections are the scalar matrices (`Matrix.mem_range_scalar_iff_commute_transvectionStruct`).

#### Row equivalence and echelon forms

**Definition (`Matrix.RowEquivalent`).** Two matrices $A$ and $B$ with rows indexed by $m$ are row equivalent when $B = G A$ for an element $G$ of the general linear group of $m$.

This is an equivalence relation, with the setoid `Matrix.RowEquivalent.setoid`. The elementary operations preserve it: `Matrix.rowEquivalent_swap`, `Matrix.rowEquivalent_rowScale` with a unit, and `Matrix.rowEquivalent_transvection`.

**Definition (`Matrix.IsRowEchelon`).** A matrix $A$, with ordered row and column types, is in row echelon form when for rows $i_1 < i_2$ and each column $j_2$, if the row $i_1$ is zero in all columns $j_1 < j_2$, then $A_{i_2 j_2} = 0$.

Below a zero row all rows are zero (`Matrix.IsRowEchelon.row_eq_zero_of_lt`). The position of the first nonzero entry of a row is described by `Matrix.IsLeadingEntry`, and `Matrix.IsReducedRowEchelon` asks in addition that each leading entry be $1$ with zeros above it. For a square matrix, `Matrix.IsRowEchelon.isUpperTriangular` says that an echelon matrix is upper triangular, so `Matrix.IsRowEchelon.det_eq` gives the determinant as the product of the diagonal. The predicate `Matrix.IsPivotedBy` records the positions of the leading entries as a function $l : m \to$ `WithTop n`, with the value $\top$ for a zero row. This function is unique (`Matrix.IsPivotedBy.unique`), and `Matrix.IsPivotedBy.rank_eq` says that the rank is the number of rows with $l(i) \ne \top$.

**Definition (`Echelon.Decomposition`).** For a matrix $A$, a lower triangular matrix $L$ with nonzero diagonal, a permutation $\sigma$ of the rows and a pivot function, `Echelon.Decomposition A L σ pivot` says that $L$ times $A$ with the rows permuted by $\sigma$ is pivoted by the function.

The structure is a certificate: a program finds $L$, $\sigma$ and the pivots, and the proof only checks them. From a certificate, `Echelon.Decomposition.rank_eq` gives the rank as the number of pivots, and `Echelon.Decomposition.prod_diag_mul_det` gives the determinant from the diagonals of $L$ and of the echelon form.

#### Transvections of a module

The basis free form of a transvection uses a linear form.

**Definition (`LinearMap.transvection`).** For a linear form $f$ on $V$ and a vector $v \in V$, `LinearMap.transvection f v` is the linear map $x \mapsto x + f(x) v$.

By `LinearMap.transvection.det`, its determinant is $1 + f(v)$. When $f(v) = 0$, the map is an automorphism `LinearEquiv.transvection`, a transvection in the strict sense, with determinant $1$ (`LinearEquiv.transvection.det_eq_one`). When $1 + f(v)$ is a unit, `LinearEquiv.dilatransvection` is the automorphism; these maps are the dilatransvections, which include the dilations of a hyperplane. The sets of all such automorphisms are `LinearEquiv.transvections` and `LinearEquiv.dilatransvections`. Over a field, `LinearEquiv.mem_dilatransvections_iff_finrank` says that $e$ is a dilatransvection if and only if $e - 1$ has rank at most $1$. The change of base ring of Volume 8 maps transvections to transvections (`LinearEquiv.transvection.baseChange`).

The theorem of Dieudonné bounds the number of factors. For an automorphism $e$ of a finite dimensional vector space, let $k$ be the codimension of the subspace of fixed vectors of $e$, the space `LinearMap.fixedSubmodule` of Chapter 1 Section 10. The automorphism is exceptional, `LinearEquiv.IsExceptional`, when it induces a homothety other than the identity on the quotient by its fixed vectors.

**Theorem (`LinearEquiv.mem_transvections_pow_mul_dilatransvections_of_not_isExceptional`).** If $e$ is not exceptional, then $e$ is the product of $k - 1$ transvections and one dilatransvection.

The module `Mathlib.LinearAlgebra.Transvection.Generation` proves it with the bounds on the dimension of the fixed vectors of a product, such as `LinearEquiv.finrank_fixedSubmodule_mul_dilatransvection_le`. The module `Mathlib.LinearAlgebra.Center` describes the center of the ring of endomorphisms: `LinearMap.commute_transvections_iff_of_basis` says that a map that commutes with all transvections of a basis is a scalar, and `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent` says that a map $f$ for which $v$ and $f(v)$ are never linearly independent is a scalar.

#### Other computations and bounds

Row reduction needs division. A division free method computes the determinant over each commutative ring. The module `Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs` implements the algorithm of Bird, which iterates one simple step $n - 1$ times on an $n \times n$ matrix and uses $O(n^4)$ operations. The step is `BirdDet.Spec.stepEntry`, and the result is `BirdDet.Spec.birdDet` for a matrix. The version `BirdDet.birdDet` works on an array of entries in row major order, which is fast to evaluate. The module `Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness` proves that the algorithm is correct: `BirdDet.det_eq_birdDet` says that `BirdDet.birdDet n A` is the determinant of the matrix with the entries of the array $A$.

The Laplace expansion of Section 1 becomes simpler when the rows add up to zero.

**Theorem (`Matrix.det_eq_sum_row_mul_submatrix_succAbove_succAbove_det`).** Let $M$ be an $(n + 1) \times (n + 1)$ matrix, and let $i_0$ and $j_0$ be indices. If each row other than the row $i_0$ has the sum $0$, then $\det M = (-1)^{i_0 + j_0} \big(\sum_j M_{i_0 j}\big) \det M'$, where $M'$ is $M$ without the row $i_0$ and the column $j_0$.

*Proof sketch.* Add all the columns other than $j_0$ to the column $j_0$. This does not change the determinant. The new column $j_0$ has the entry $\sum_j M_{i_0 j}$ in the row $i_0$ and the entry $0$ in the other rows, so the expansion along it has one term. $\square$

The version for columns is `Matrix.det_eq_sum_column_mul_submatrix_succAbove_succAbove_det`. For a matrix with $n + 1$ rows and $n$ columns whose rows add up to zero, the maximal minors without one row agree up to sign (`Matrix.submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det`). These results appear in the matrix tree theorem, where the rows of the Laplacian matrix of a graph add up to zero.

The Leibniz formula also gives a bound. For an absolute value $|\cdot|$ on a nontrivial commutative ring, if each entry of an $n \times n$ matrix $A$ satisfies $|A_{ij}| \le x$, then $|\det A| \le n! \, x^n$ (`Matrix.det_le`). The variants `Matrix.det_sum_le` and `Matrix.det_sum_smul_le` treat sums of matrices and linear combinations of them. The theory of number fields uses these bounds.

Polynomial matrices relate the determinant to its coefficients. For square matrices $A$ and $B$ over a commutative ring, $\det(X A + B)$ is a polynomial of degree at most $|n|$ (`Polynomial.natDegree_det_X_add_C_le`). Its constant coefficient is $\det B$ (`Polynomial.coeff_det_X_add_C_zero`), and its coefficient of degree $|n|$ is $\det A$ (`Polynomial.coeff_det_X_add_C_card`). For $A = 1$, the polynomial is monic (`Polynomial.leadingCoeff_det_X_one_add_C`); this is the characteristic polynomial of $-B$ in Chapter 5. The generic matrix `Matrix.mvPolynomialX m n R` has the variable $X_{ij}$ as its entry $(i, j)$, in the ring of polynomials of Volume 6 in the variables $X_{ij}$. Each matrix is a specialization of it (`Matrix.mvPolynomialX_mapMatrix_eval`), and its determinant is not zero over a nontrivial ring (`Matrix.det_mvPolynomialX_ne_zero`). Thus a polynomial identity in the entries can be proved for the generic matrix and then specialized.

Last, for a nonzero free module $M$ of finite rank, the determinant of the zero endomorphism is $0$ (`LinearMap.det_zero''`). The hypothesis that $M$ is not zero is necessary, because on the zero module the zero map is the identity, with determinant $1$.

#### Common errors

1. `Matrix.transvection i j c` adds $c$ times the row $j$ to the row $i$ when it multiplies on the left. On the right, it adds $c$ times the column $i$ to the column $j$.
2. `Matrix.permMatrix_mul` reverses the order: $P_{\sigma \tau} = P_\tau P_\sigma$.
3. `Matrix.RowEquivalent` uses all invertible matrices, not only products of elementary matrices. Over a field the two notions agree, but the definition does not depend on this.

### Exercises

1. (A) Compute `Matrix.transvection 0 1 c * !![a, b; d, e]` for $2 \times 2$ matrices.
2. (A) Show that `Matrix.swap R i j` has determinant $-1$ for $i \ne j$, with `Matrix.det_permutation`.
3. (B) Show that each $2 \times 2$ matrix over a field with determinant $1$ is a product of transvections.
4. (B) Prove that a square matrix in row echelon form with a zero row has determinant $0$.
5. (B) Show that $x \mapsto x + f(x) v$ with $f(v) = 0$ has the inverse $x \mapsto x - f(x) v$.
6. (C) Use `Matrix.diagonal_transvection_induction_of_det_ne_zero` to prove that a function $\phi$ from the invertible matrices over a field to a commutative group with $\phi(A B) = \phi(A) \phi(B)$ and $\phi(T) = 1$ for each transvection $T$ factors through the determinant.

### Reference

<?reference?>
