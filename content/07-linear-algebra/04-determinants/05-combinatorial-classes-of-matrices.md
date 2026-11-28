---
title: Totally unimodular, Hadamard, stochastic and irreducible matrices
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
  - Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg
  - Mathlib.LinearAlgebra.Matrix.Permanent
  - Mathlib.LinearAlgebra.Matrix.HadamardMatrix
  - Mathlib.LinearAlgebra.Matrix.Stochastic
  - Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
explains:
  E2: [Matrix.IsTotallyUnimodular, Matrix.isTotallyUnimodular_iff, Matrix.IsTotallyNonneg, Matrix.permanent, Matrix.IsHadamard, Matrix.IsHadamard.det_mul_star_det, Matrix.IsHadamard.four_dvd_card, Matrix.rowStochastic, Matrix.IsIrreducible, Matrix.IsPrimitive]
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

## Totally unimodular, Hadamard, stochastic and irreducible matrices

### Overview

Combinatorics, optimization and probability use classes of matrices that are defined by conditions on the entries or on the minors. This section describes six of them. A totally unimodular matrix has all square minors in $\{-1, 0, 1\}$; it is the matrix of a linear program with integer optimal solutions. A totally nonnegative matrix has all minors with increasing indices nonnegative. The permanent is the determinant without the signs. A Hadamard matrix has entries $\pm 1$ and orthogonal rows. A stochastic matrix has nonnegative entries and rows of sum $1$; it is the matrix of a Markov chain. An irreducible matrix is nonnegative, with a strongly connected graph of positive entries; it is the setting of the theorem of Perron and Frobenius.

Most of these classes are predicates on matrices, defined with the determinant of Section 1 and the submatrices of Chapter 3. The stochastic matrices are submonoids of the matrix monoid.

### The library around it

#### Totally unimodular matrices

**Definition (`Matrix.IsTotallyUnimodular`).** A matrix $A$ of type `Matrix m n R` over a commutative ring is totally unimodular when, for each $k$ and each pair of injective maps $f : \text{Fin } k \to m$ and $g : \text{Fin } k \to n$, the determinant of `A.submatrix f g` is in the range of the cast from `SignType`, that is, in $\{-1, 0, 1\}$.

The matrix need not be square. The condition with injective maps is the condition on the square minors. The maps are not ordered, so a minor can come with its rows permuted, but a permutation changes only the sign of the determinant.

**Theorem (`Matrix.isTotallyUnimodular_iff`).** In the definition, the hypothesis that $f$ and $g$ are injective can be removed.

*Proof sketch.* If $f$ or $g$ is not injective, then the submatrix has two equal rows or two equal columns. Its determinant is then $0$, which is in $\{-1, 0, 1\}$. $\square$

The version `Matrix.isTotallyUnimodular_iff_fintype` takes square submatrices indexed by any finite type. The case $k = 1$ gives `Matrix.IsTotallyUnimodular.apply`: each entry is $-1$, $0$ or $1$. The class is closed under submatrices (`Matrix.IsTotallyUnimodular.submatrix`), under the transpose (`Matrix.IsTotallyUnimodular.transpose`) and under reindexing (`Matrix.IsTotallyUnimodular.reindex`). The matrices with no rows or no columns are totally unimodular (`Matrix.emptyRows_isTotallyUnimodular`, `Matrix.emptyCols_isTotallyUnimodular`).

In linear programming the constraint matrix often has an identity block beside it. The lemmas `Matrix.fromRows_one_isTotallyUnimodular_iff` and `Matrix.fromCols_one_isTotallyUnimodular_iff` say that this block does not change the property: the block matrix with rows $A$ and $1$ is totally unimodular if and only if $A$ is. A row of zeros also does not change it (`Matrix.fromRows_replicateRow0_isTotallyUnimodular_iff`). The general form is `Matrix.IsTotallyUnimodular.fromRows_unitlike`, for added rows with at most one nonzero entry, and this entry in $\{-1, 1\}$.

#### Totally nonnegative matrices

**Definition (`Matrix.IsTotallyNonneg`).** A square matrix $M$ indexed by a linear order, over an ordered commutative ring, is totally nonnegative when $0 \le \det$ `M.submatrix rows cols` for all strictly increasing maps $\text{rows}, \text{cols} : \text{Fin } k \to \iota$.

Here the order of the indices matters, because a permutation of rows can change the sign of a minor. The entries are nonnegative (`Matrix.IsTotallyNonneg.nonneg`, the case $k = 1$). The identity and the diagonal matrices with nonnegative entries are totally nonnegative (`Matrix.IsTotallyNonneg.one`, `Matrix.IsTotallyNonneg.diagonal`), and `Matrix.isTotallyNonneg_diagonal_iff` gives the converse for diagonal matrices. The class is closed under nonnegative scalar multiples (`Matrix.IsTotallyNonneg.smul`), under the transpose and the conjugate transpose (`Matrix.IsTotallyNonneg.transpose`, `Matrix.IsTotallyNonneg.conjTranspose`), and under submatrices with strictly increasing maps (`Matrix.IsTotallyNonneg.submatrix`). Examples from the theory are the Vandermonde matrices with increasing positive nodes and the matrices of Pascal.

#### The permanent

**Definition (`Matrix.permanent`).** For a square matrix $M$ over a commutative semiring, `Matrix.permanent M` is $\sum_{\sigma} \prod_i M_{\sigma(i), i}$, the sum over all permutations $\sigma$ of the index type.

This is the formula of Leibniz without the signs, so it is defined over $\mathbb{N}$. The permanent of a $0$-$1$ matrix counts the perfect matchings of the associated bipartite graph. It shares some rules with the determinant: `Matrix.permanent_diagonal` gives the product of the diagonal, `Matrix.permanent_one` the value $1$, `Matrix.permanent_zero` the value $0$ for a nonempty index type, `Matrix.permanent_transpose` the invariance under the transpose, and `Matrix.permanent_smul` the factor $c^n$ for $c M$. Other rules are different: a permutation of the rows does not change the permanent (`Matrix.permanent_permute_rows`, `Matrix.permanent_permute_cols`), and the permanent is not multiplicative. The rule for one row is `Matrix.permanent_updateRow_smul`. Over the empty index type, the permanent is $1$ (`Matrix.permanent_isEmpty`).

#### Hadamard matrices

**Definition (`Matrix.IsHadamard`).** A square matrix $A$ over a ring with a star operation is a Hadamard matrix when each entry is unitary, $A A^* = n \cdot 1$ and $A^* A = n \cdot 1$, where $n$ is the number of indices.

Over $\mathbb{Z}$ or $\mathbb{R}$, with the trivial star, a unitary entry is $1$ or $-1$, so this is the classical notion: a matrix of signs with orthogonal rows. Over $\mathbb{C}$, it gives the complex Hadamard matrices with entries of absolute value $1$. The fields of the structure are `Matrix.IsHadamard.apply_mem`, `Matrix.IsHadamard.mul_conjTranspose` and `Matrix.IsHadamard.conjTranspose_mul`. The two product conditions say that $A$ commutes with $A^*$ (`Matrix.IsHadamard.isStarNormal`). The class is closed under the transpose, the negation and reindexing (`Matrix.IsHadamard.transpose`, `Matrix.IsHadamard.neg`, `Matrix.IsHadamard.reindex`).

**Theorem (`Matrix.IsHadamard.det_mul_star_det`).** Over a commutative ring, a Hadamard matrix of order $n$ has $\det A \cdot \overline{\det A} = n^n$.

*Proof.* Take determinants in $A A^* = n \cdot 1$. The left side is $\det A \cdot \det A^* = \det A \cdot \overline{\det A}$, and the right side is $n^n \det 1 = n^n$. $\square$

So a real Hadamard matrix has $|\det A| = n^{n/2}$. This is the bound of Hadamard for matrices with entries in $[-1, 1]$, and Hadamard matrices are the matrices with equality. Over a reduced ring with $n \ne 0$, the determinant is not zero (`Matrix.IsHadamard.det_ne_zero`).

**Theorem (`Matrix.IsHadamard.four_dvd_card`).** If $A$ is an integer Hadamard matrix of order $n > 2$, then $4$ divides $n$.

*Proof sketch.* Multiply each column by the sign of its entry in the first row, so that the first row has all entries $1$; this keeps the Hadamard property. Take the rows $1$, $2$ and $3$. Count the columns by the four patterns of signs in the rows $2$ and $3$. The orthogonality of the three rows gives three linear equations on the four counts, and their solution makes each count equal to $n/4$. $\square$

The conjecture of Hadamard, that a Hadamard matrix of order $n$ exists for each $n$ divisible by $4$, is open. The construction of Sylvester gives the orders $2^k$, with `Matrix.IsHadamard.kronecker`: the Kronecker product of Chapter 3 Section 8 of two Hadamard matrices is a Hadamard matrix.

#### Stochastic matrices

**Definition (`Matrix.rowStochastic`).** For an ordered semiring $R$ and a finite type $n$, `Matrix.rowStochastic R n` is the submonoid of `Matrix n n R` of the matrices $M$ with nonnegative entries and $M \mathbf{1} = \mathbf{1}$, where $\mathbf{1}$ is the vector of ones.

The condition $M \mathbf{1} = \mathbf{1}$ says that each row has sum $1$; this form is `Matrix.mem_rowStochastic_iff_sum`, and the form with the vector is `Matrix.mem_rowStochastic`. It is a submonoid because $(M N) \mathbf{1} = M (N \mathbf{1}) = M \mathbf{1} = \mathbf{1}$. The entries are at most $1$ (`Matrix.le_one_of_mem_rowStochastic`), and the permutation matrices are stochastic (`Matrix.permMatrix_mem_rowStochastic`). The set is convex (`Matrix.convex_rowStochastic`). A row stochastic matrix sends a probability vector $x$, a nonnegative row vector with sum $1$, to a probability vector $x M$ (`Matrix.vecMul_dotProduct_one_eq_one_rowStochastic`). This is one step of a Markov chain with the transition matrix $M$.

The submonoid `Matrix.colStochastic` is the same with columns, and `Matrix.transpose_mem_colStochastic_iff_mem_rowStochastic` relates the two. The lemma `Matrix.sum_mulVec_of_mem_colStochastic` says that a column stochastic matrix keeps the sum of the entries of a column vector. A matrix in both submonoids is doubly stochastic. The theorem of Birkhoff, that the doubly stochastic matrices are the convex combinations of permutation matrices, is in the folder `Mathlib/Analysis/Convex`.

#### Irreducible and primitive matrices

A square matrix $A$ over an ordered ring gives the quiver `Matrix.toQuiver A` on the index type, with an arrow from $i$ to $j$ when $0 < A_{ij}$.

**Definition (`Matrix.IsIrreducible`).** A square matrix $A$ over a linearly ordered ring is irreducible when all its entries are nonnegative and its quiver is strongly connected: for all $i$ and $j$ there is a path of positive length from $i$ to $j$.

**Definition (`Matrix.IsPrimitive`).** A square matrix $A$ is primitive when all its entries are nonnegative and, for some $k > 0$, all the entries of $A^k$ are positive.

The link between the two is the meaning of the powers. For a nonnegative $A$, the entry $(A^k)_{ij}$ is a sum of products $A_{i i_1} A_{i_1 i_2} \cdots A_{i_{k-1} j}$, and it is positive if and only if one product is positive, that is, if and only if there is a path of length $k$ from $i$ to $j$. This is `Matrix.pow_apply_pos_iff_nonempty_path`. From it, `Matrix.isIrreducible_iff_exists_pow_pos` says that a nonnegative $A$ is irreducible if and only if for each pair $(i, j)$ some positive power has a positive entry at $(i, j)$. A primitive matrix has one power that works for all pairs, so it is irreducible (`Matrix.IsPrimitive.isIrreducible`). The converse is false: the matrix `!![0, 1; 1, 0]` is irreducible, and its powers alternate between it and the identity, so no power is positive.

On a nontrivial index type, each row of an irreducible matrix has a positive entry (`Matrix.IsIrreducible.exists_pos`). The transpose of an irreducible matrix is irreducible (`Matrix.IsIrreducible.transpose`), because reversing all arrows keeps a quiver strongly connected. The theorem of Perron and Frobenius, on the positive eigenvector of an irreducible matrix, is not in this version of Mathlib; the definitions of this module are the start of it.

#### Common errors

1. `Matrix.IsTotallyUnimodular` takes all square submatrices, but `Matrix.IsTotallyNonneg` takes only the submatrices with strictly increasing indices. The two definitions are not of the same form.
2. The permanent is not multiplicative. There is no lemma of the form `permanent (A * B) = permanent A * permanent B`, and the statement is false for $2 \times 2$ matrices.
3. `Matrix.rowStochastic R n` is a submonoid, not a predicate. Write `M ∈ Matrix.rowStochastic R n`, and use `Matrix.mem_rowStochastic_iff_sum` to get the conditions on the entries.

### Exercises

1. (A) Show that `!![1, 1; 1, -1]` is a Hadamard matrix over $\mathbb{Z}$, and compute its determinant.
2. (A) Compute the permanent of the $3 \times 3$ matrix with all entries $1$, and explain the value with permutations.
3. (B) Show that the product of two row stochastic matrices is row stochastic, directly from the sums of the rows.
4. (B) Prove that the incidence matrix of a directed graph, with $1$ and $-1$ for the two ends of each edge, has entries in $\{-1, 0, 1\}$, and check that it is totally unimodular for a directed triangle.
5. (B) Give a $2 \times 2$ example with $\operatorname{perm}(A B) \ne \operatorname{perm}(A) \operatorname{perm}(B)$.
6. (C) Show that the matrix `!![1, 1; 1, 0]` over $\mathbb{Z}$ is primitive, and that the matrix `!![0, 1; 1, 0]` is irreducible and not primitive.

### Reference

<?reference?>
