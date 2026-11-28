---
title: Kronecker, Hadamard and circulant matrices
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.Kronecker
  - Mathlib.LinearAlgebra.Matrix.Hadamard
  - Mathlib.LinearAlgebra.Matrix.Circulant
  - Mathlib.LinearAlgebra.Matrix.WithConv
explains:
  E2: [Matrix.kroneckerMap, Matrix.kronecker, Matrix.mul_kronecker_mul, Matrix.det_kronecker, Matrix.trace_kronecker, Matrix.kroneckerTMul, Matrix.hadamard, Matrix.sum_hadamard_eq, Matrix.circulant, Matrix.circulant_mul_comm]
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

## Kronecker, Hadamard and circulant matrices

### Overview

The product of Section 1 is one way to combine two matrices. This section describes two other products and one family of structured matrices. The Kronecker product of an $l \times m$ matrix $A$ and an $n \times p$ matrix $B$ is the $(l n) \times (m p)$ matrix of all products $A_{ij} B_{kl}$; it is the matrix of the tensor product of two linear maps. The Hadamard product of two matrices of the same shape multiplies them entry by entry. A circulant matrix has each row equal to the row above it, shifted by one place.

Mathlib indexes the Kronecker product by pairs: the rows of $A \otimes B$ are indexed by $l \times n$ and the columns by $m \times p$. So no arithmetic on indices is necessary, and the formulas are short.

### The library around it

#### The Kronecker product

The general construction takes a function of two entries.

**Definition (`Matrix.kroneckerMap`).** For a function $f : \alpha \to \beta \to \gamma$, a matrix $A$ of type `Matrix l m α` and a matrix $B$ of type `Matrix n p β`, `Matrix.kroneckerMap f A B` is the matrix of type `Matrix (l × n) (m × p) γ` with the entry $f(A_{i_1 j_1}, B_{i_2 j_2})$ at $((i_1, i_2), (j_1, j_2))$.

The lemma `Matrix.kroneckerMap_apply` states this. With $f$ the product, the result is the Kronecker product `Matrix.kronecker`, with the notation `A ⊗ₖ B` in the scope Kronecker, and `Matrix.kronecker_apply` gives its entries. With $f$ the tensor product of two elements, the result is `Matrix.kroneckerTMul`, a matrix with entries in the tensor product $\alpha \otimes_R \beta$ of Volume 8, with the notation `A ⊗ₖₜ B` and the entries `Matrix.kroneckerTMul_apply`. Most lemmas below exist for both forms.

The general map has the lemmas that need only conditions on $f$: `Matrix.kroneckerMap_transpose`, `Matrix.kroneckerMap_map`, `Matrix.kroneckerMap_reindex`, `Matrix.kroneckerMap_submatrix_submatrix`, and the linearity lemmas `Matrix.kroneckerMap_add_left` and `Matrix.kroneckerMap_smul_left` when $f$ is additive or linear in each argument. For a bilinear $f$, `Matrix.kroneckerMapBilinear` is the bilinear map of matrices, and `Matrix.kroneckerBilinear` is the case of the product in an algebra. The Kronecker product of two diagonal matrices is diagonal (`Matrix.diagonal_kronecker_diagonal`), of two matrix units is a matrix unit (`Matrix.single_kronecker_single`), and of two identity matrices is the identity (`Matrix.one_kronecker_one`). With an identity on one side, the result is a block diagonal matrix: `Matrix.kronecker_one` says that $A \otimes 1$ is block diagonal with copies of $A$, and `Matrix.one_kronecker` says that $1 \otimes B$ is the same after a reindexing.

The main algebraic rule is the mixed product property.

**Theorem (`Matrix.mul_kronecker_mul`).** Over a commutative semiring, $(A B) \otimes (A' B') = (A \otimes A')(B \otimes B')$.

*Proof.* Compare the entries at $((i, i'), (k, k'))$. The left side is $\left(\sum_j A_{ij} B_{jk}\right) \left(\sum_{j'} A'_{i'j'} B'_{j'k'}\right)$. The right side is $\sum_{(j, j')} A_{ij} A'_{i'j'} B_{jk} B'_{j'k'}$. Expand the product of the two sums and reorder the four factors, which is possible because the semiring is commutative. $\square$

The general form is `Matrix.kroneckerMapBilinear_mul_mul`, for a bilinear map $f$ with a condition of compatibility with products. From the mixed product property, $A \otimes B$ is invertible when $A$ and $B$ are, with inverse $A^{-1} \otimes B^{-1}$. The Kronecker product is associative up to the reindexing of $(l \times n) \times q$ as $l \times (n \times q)$ (`Matrix.kronecker_assoc`).

The two numerical invariants of square matrices have simple formulas.

**Theorem (`Matrix.trace_kronecker`).** For square matrices over a commutative semiring, $\operatorname{tr}(A \otimes B) = \operatorname{tr}(A) \operatorname{tr}(B)$.

*Proof.* The diagonal entries of $A \otimes B$ are $A_{ii} B_{jj}$ for the pairs $(i, j)$. Their sum is $\sum_i \sum_j A_{ii} B_{jj} = \left(\sum_i A_{ii}\right) \left(\sum_j B_{jj}\right)$. $\square$

**Theorem (`Matrix.det_kronecker`).** For an $m \times m$ matrix $A$ and an $n \times n$ matrix $B$ over a commutative ring, $\det(A \otimes B) = \det(A)^{n} \det(B)^{m}$.

*Proof sketch.* Write $A \otimes B = (A \otimes 1)(1 \otimes B)$ with the mixed product property. The matrix $A \otimes 1$ is block diagonal with $n$ copies of $A$ after a reindexing, so its determinant is $\det(A)^n$ by Chapter 4. In the same way $\det(1 \otimes B) = \det(B)^m$. $\square$

The tensor versions are `Matrix.trace_kroneckerTMul` and `Matrix.det_kroneckerTMul`. The link with vectorization is `Matrix.kronecker_mulVec_vec` of Section 6.

#### The Hadamard product

**Definition (`Matrix.hadamard`).** For two matrices $A$ and $B$ of the same shape, `Matrix.hadamard A B` is the matrix with the entries $A_{ij} B_{ij}$. The notation is `A ⊙ B`.

The lemma `Matrix.hadamard_apply` states this. The product is commutative (`Matrix.hadamard_comm`) when the entries commute, associative (`Matrix.hadamard_assoc`), and distributive over the sum (`Matrix.hadamard_add`, `Matrix.add_hadamard`). The unit of the Hadamard product is the matrix with all entries $1$, which is `Matrix.of 1`, not the identity matrix: `Matrix.hadamard_of_one`. The product with the identity keeps the diagonal: `Matrix.hadamard_one` says that $A \odot 1$ is the diagonal matrix of the diagonal of $A$. Other rules are `Matrix.diagonal_hadamard_diagonal`, `Matrix.transpose_hadamard`, `Matrix.conjTranspose_hadamard` and `Matrix.single_hadamard_single_eq`.

**Theorem (`Matrix.sum_hadamard_eq`).** The sum of all entries of $A \odot B$ is $\operatorname{tr}(A B^T)$.

*Proof.* The entry $(i, i)$ of $A B^T$ is $\sum_j A_{ij} B_{ij}$. The sum over $i$ is the sum of all entries $A_{ij} B_{ij}$ of $A \odot B$. $\square$

The weighted form is `Matrix.dotProduct_vecMul_hadamard`, which writes $(v (A \odot B)) \cdot w$ as a trace with diagonal matrices of $v$ and $w$.

The module `Mathlib.LinearAlgebra.Matrix.WithConv` puts the Hadamard product into the type synonym `WithConv` of the folder `Mathlib/Algebra`. On `WithConv (Matrix m n α)`, the product is the Hadamard product (`convMul_def`), the unit is `Matrix.of 1` (`convOne_def`), and the star is the entrywise star without a transpose (`intrinsicStar_def`). With these, the type is a ring (`instRingWithConvMatrix`), commutative when $\alpha$ is commutative, and a star ring. The type synonym keeps this ring structure apart from the usual one, so the two products never conflict. The equivalence `WithConv.matrixToLin'StarAlgEquiv` identifies it with the convolution ring of linear maps $(n \to \alpha) \to (m \to \alpha)$, and `Matrix.toLin'_hadamard` is the statement for one product. For example `Matrix.isSymm_iff_intrinsicStar_toLin'` describes the symmetric matrices with this star.

#### Circulant matrices

**Definition (`Matrix.circulant`).** For an index type $n$ with a subtraction and a vector $v : n \to \alpha$, `Matrix.circulant v` is the matrix with the entry $v(i - j)$ at $(i, j)$.

The lemma `Matrix.circulant_apply` states this, and `Matrix.circulant_col_zero_eq` says that the first column is $v$. The usual index type is `Fin n` or `ZMod n` with the subtraction modulo $n$; then each row is the row above it moved by one place to the right. The map $v \mapsto$ `Matrix.circulant v` is injective (`Matrix.circulant_injective`) and linear (`Matrix.circulant_add`, `Matrix.circulant_smul`). The vector $e_0$ gives the identity (`Matrix.circulant_single_one`). The transpose is the circulant matrix of $i \mapsto v(-i)$ (`Matrix.transpose_circulant`), so `Matrix.circulant_isSymm_iff` says that the matrix is symmetric if and only if $v(-i) = v(i)$ for all $i$.

The product of two circulant matrices is circulant: `Matrix.circulant_mul` says that $C(v) C(w) = C(C(v) w)$, for an index type that is an additive group.

**Theorem (`Matrix.circulant_mul_comm`).** When the product of $\alpha$ is commutative and the finite index type is a commutative additive group, two circulant matrices commute.

*Proof.* The entry $(i, k)$ of $C(v) C(w)$ is $\sum_j v(i - j) w(j - k)$. Substitute $j' = i + k - j$; this is a bijection of the index group. The sum becomes $\sum_{j'} v(j' - k) w(i - j')$, which is the entry $(i, k)$ of $C(w) C(v)$ after the product of the entries is commuted. $\square$

The lemmas such as `Matrix.Fin.circulant_mul_comm` are versions for the index type `Fin n`, which is an additive group only for $n > 0$; the case $n = 0$ is trivial. So the circulant matrices form a commutative subalgebra of the square matrices, isomorphic to the group algebra of the cyclic group. This is why the discrete Fourier transform diagonalizes all circulant matrices at once.

#### Common errors

1. The Kronecker product has rows indexed by `l × n`, not by `Fin (l * n)`. To compare it with a textbook matrix of size $l n$, reindex with `finProdFinEquiv`.
2. The identity matrix is not the unit of the Hadamard product. Use `Matrix.of 1` with `Matrix.hadamard_of_one`.
3. The notation `A ⊗ₖ B` needs `open Kronecker`. Without it, the expression is a parse error.

### Exercises

1. (A) Compute the Kronecker product of `!![1, 2; 3, 4]` and the $2 \times 2$ identity matrix.
2. (A) Show that $A \odot B = B \odot A$ for matrices over a commutative ring, with `Matrix.hadamard_comm`.
3. (B) Prove from `Matrix.mul_kronecker_mul` that $A \otimes B$ is invertible when $A$ and $B$ are invertible.
4. (B) Compute $\det(A \otimes B)$ for $A = \operatorname{diag}(2, 3)$ and $B = \operatorname{diag}(1, 5, 7)$ directly and with `Matrix.det_kronecker`.
5. (B) Write the $3 \times 3$ circulant matrix of $v = (a, b, c)$ indexed by `Fin 3`, and check that it commutes with the circulant matrix of $(0, 1, 0)$.
6. (C) Let $\zeta$ be a primitive $n$-th root of unity in $\mathbb{C}$. Show that the vector $(1, \zeta, \zeta^2, \dots, \zeta^{n-1})$ is an eigenvector of each circulant matrix indexed by `Fin n`.

### Reference

<?reference?>
