---
title: Matrix notation, rows, columns and reindexing
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.Notation
  - Mathlib.LinearAlgebra.Matrix.RowCol
  - Mathlib.LinearAlgebra.Matrix.Reindex
  - Mathlib.LinearAlgebra.Matrix.Unique
  - Mathlib.LinearAlgebra.Matrix.Array
  - Mathlib.LinearAlgebra.Matrix.StdBasis
  - Mathlib.LinearAlgebra.Matrix.Diagonal
  - Mathlib.LinearAlgebra.Matrix.DotProduct
  - Mathlib.LinearAlgebra.Matrix.Vec
explains:
  E2: [Matrix.eta_fin_two, Matrix.mul_fin_two, Matrix.replicateCol, Matrix.updateRow, Matrix.reindexLinearEquiv, Matrix.uniqueRingEquiv, Matrix.stdBasis, Matrix.vec, Matrix.kronecker_mulVec_vec, dotProduct_self_eq_zero]
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

## Matrix notation, rows, columns and reindexing

### Overview

Sections 1 and 4 define matrices and their algebra. This section collects the small tools that make concrete computation with matrices possible: the notation `!![a, b; c, d]` and its simplification lemmas, matrices with one row or one column, the replacement of one row or column, the change of index types, the standard basis of a matrix space, the linear map of a diagonal matrix, the positivity properties of the dot product, and the vectorization of a matrix.

Each topic is a short module in the folder `Mathlib/LinearAlgebra/Matrix`. The modules do not depend on each other much, and a proof about a concrete matrix often uses several of them at once.

### The library around it

#### Concrete matrices

The module `Mathlib.LinearAlgebra.Matrix.Notation` gives the notation `!![a, b; c, d]` for the matrix with rows $(a, b)$ and $(c, d)$. It is the matrix `Matrix.of ![![a, b], ![c, d]]`, where `![a, b]` is the vector of Volume 3 built with `Matrix.vecCons`. The entries of the notation simplify with the lemmas `Matrix.cons_val_zero` and `Matrix.cons_val_one`, and the instance `Matrix.repr` prints a matrix in the same notation.

**Theorem (`Matrix.eta_fin_two`).** Each $2 \times 2$ matrix $A$ is equal to `!![A 0 0, A 0 1; A 1 0, A 1 1]`.

*Proof.* Two matrices are equal when their entries are equal (`Matrix.ext`). The index type `Fin 2` has the two elements $0$ and $1$, and the entries of the notation at these indices are the four given entries. $\square$

The lemma `Matrix.eta_fin_three` is the same statement for $3 \times 3$ matrices. With these lemmas, a statement about a general $2 \times 2$ matrix becomes a statement about four entries. The operations then compute in the notation.

**Theorem (`Matrix.mul_fin_two`).** The product of `!![a₁₁, a₁₂; a₂₁, a₂₂]` and `!![b₁₁, b₁₂; b₂₁, b₂₂]` is the matrix with the entries $a_{i1} b_{1j} + a_{i2} b_{2j}$.

The other lemmas of this kind are `Matrix.mul_fin_three`, `Matrix.one_fin_two`, `Matrix.one_fin_three`, `Matrix.diagonal_fin_two`, `Matrix.natCast_fin_two` and `Matrix.ofNat_fin_two`. For products with vectors, `Matrix.cons_mulVec`, `Matrix.mulVec_cons`, `Matrix.cons_vecMul` and `Matrix.vecMul_cons` reduce a product to the first row or entry and a product of smaller size. The dot products of concrete vectors are `Matrix.vec2_dotProduct` and `Matrix.vec3_dotProduct`, and the operations on vectors are `Matrix.vec2_add` and `Matrix.smul_vec2`. In practice, the simplifier with these lemmas, or `Matrix.mulᵣ_eq` of Section 4, computes a concrete product.

The module `Mathlib.LinearAlgebra.Matrix.Array` is for programs. The function `Matrix.ofArray` makes a matrix from an array of arrays, and `Matrix.toArray` makes the array from a matrix. The lemmas `Matrix.ofArray_toArray` and `Matrix.toArray_ofArray` say that the two functions are inverse, and `Matrix.size_toArray` gives the size.

#### Rows and columns

A vector $v : m \to \alpha$ gives a matrix with one column.

**Definition (`Matrix.replicateCol`).** For a type $\iota$ and a vector $v : m \to \alpha$, `Matrix.replicateCol ι v : Matrix m ι α` is the matrix whose columns are all equal to $v$.

The usual case is a type $\iota$ with one element, which gives a column matrix. The matrix `Matrix.replicateRow` is the same with rows. The lemma `Matrix.transpose_replicateCol` exchanges the two, `Matrix.replicateCol_mulVec` computes the column of a product with a vector, and `Matrix.replicateRow_mul_replicateCol` says that a row times a column is a $1 \times 1$ matrix with the dot product as entry. In the other order, `Matrix.vecMulVec_eq` says that a column times a row is the outer product `Matrix.vecMulVec`.

To change one row, there is a separate operation.

**Definition (`Matrix.updateRow`).** For a matrix $M$, an index $i$ and a vector $b$, `M.updateRow i b` is the matrix $M$ with the row $i$ replaced by $b$.

The lemmas `Matrix.updateRow_self` and `Matrix.updateRow_ne` give the rows of the result, and `Matrix.updateRow_apply` gives its entries. The operation `Matrix.updateCol` changes one column, and `Matrix.updateCol_transpose` relates the two through the transpose. The products behave well: `Matrix.updateRow_mul` says that changing a row of $M$ changes the same row of $M N$, and `Matrix.mul_updateCol` is the version for columns. Cramer's rule in Chapter 4 uses this operation, because the numerator of the rule is the determinant of a matrix with one column replaced. The lemma `Matrix.single_eq_updateRow_zero` writes a matrix unit of Section 5 as the zero matrix with one row changed.

#### Reindexing

A matrix is a function of two indices. An equivalence of index types gives an equivalence of matrix types.

**Definition (`Matrix.reindexLinearEquiv`).** For a semiring $R$, an $R$-module $A$ and equivalences $e_m : m \simeq m'$ and $e_n : n \simeq n'$, `Matrix.reindexLinearEquiv R A eₘ eₙ` is the linear equivalence between `Matrix m n A` and `Matrix m' n' A` that composes a matrix with the inverses of $e_m$ and $e_n$.

As a function it is `Matrix.reindex eₘ eₙ` (`Matrix.coe_reindexLinearEquiv`), and `Matrix.reindex` is `Matrix.submatrix` with the inverse equivalences. The rules `Matrix.reindexLinearEquiv_refl_refl`, `Matrix.reindexLinearEquiv_trans_reindexLinearEquiv` and `Matrix.symm_reindexLinearEquiv` say that reindexing respects identities, composition and inverses. It also respects products: `Matrix.reindexLinearEquiv_mul` and `Matrix.reindexLinearEquiv_one`.

For square matrices with the same equivalence on both sides, the product is preserved, so there are stronger structures: `Matrix.reindexAddEquiv`, `Matrix.reindexRingEquiv`, `Matrix.reindexAlgEquiv` and `Matrix.reindexStarAlgEquiv`. The determinant does not change: `Matrix.det_reindexAlgEquiv` and `Matrix.det_reindexLinearEquiv_self`. The typical use is to go from a matrix indexed by a finite type $\iota$ to a matrix indexed by `Fin n`, with the equivalence `Fintype.equivFin`. The lemmas `Matrix.updateRow_reindex` and `Matrix.reindex_updateRow` move a row change through a reindexing.

A matrix indexed by a type with exactly one element has one entry.

**Definition (`Matrix.uniqueRingEquiv`).** For a type $m$ with a unique element, `Matrix.uniqueRingEquiv : Matrix m m A ≃+* A` sends a matrix to its single entry.

The module `Mathlib.LinearAlgebra.Matrix.Unique` also gives the plain equivalence `Matrix.uniqueEquiv` for rectangular matrices, and the structured versions `Matrix.uniqueAddEquiv`, `Matrix.uniqueLinearEquiv` and `Matrix.uniqueAlgEquiv`.

#### The standard basis

The matrix units of Section 5 form a basis of the matrix space.

**Definition (`Matrix.stdBasis`).** For a semiring $R$ and finite types $m$ and $n$, `Matrix.stdBasis R m n : Module.Basis (m × n) R (Matrix m n R)` is the basis whose vector at $(i, j)$ is the matrix unit with entry $1$ at $(i, j)$.

The lemma `Matrix.stdBasis_eq_single` states this, with the matrix unit `Matrix.single i j 1`. From it, the dimension of `Matrix m n R` over a field is $|m| \cdot |n|$. For matrices with entries in a free module $M$ with a basis $b$, `Module.Basis.matrix` gives the basis of the matrices `Matrix.single i j (b k)` (`Module.Basis.matrix_apply`), and the instance `Module.Free.matrix` says that the matrix module is free.

#### Diagonal matrices as linear maps

The module `Mathlib.LinearAlgebra.Matrix.Diagonal` describes the linear map $R^n \to R^n$ of a diagonal matrix with entries $w_i$. By `Matrix.diagonal_toLin'`, it multiplies the coordinate $i$ by $w_i$. The lemma `Matrix.proj_diagonal` states the same for each coordinate, and `Matrix.diagonal_comp_single` says that the basis vector $e_i$ goes to $w_i e_i$. Over a field, the kernel is spanned by the $e_i$ with $w_i = 0$ (`Matrix.ker_diagonal_toLin'`), the range by the $e_i$ with $w_i \ne 0$ (`Matrix.range_diagonal`), and so `LinearMap.rank_diagonal` says that the rank is the number of nonzero diagonal entries.

#### The dot product and positivity

The dot product `v ⬝ᵥ w` is defined in Volume 3. The module `Mathlib.LinearAlgebra.Matrix.DotProduct` proves the facts that need an order or a star operation.

**Theorem (`dotProduct_self_eq_zero`).** In a linearly ordered ring, $v \cdot v = 0$ if and only if $v = 0$.

*Proof.* The dot product $v \cdot v$ is the sum of the squares $v_i^2$. Each square is nonnegative, and a sum of nonnegative terms is zero only when each term is zero. A square is zero only when the element is zero. $\square$

For a star ring, the matching statements are `dotProduct_star_self_eq_zero` and `dotProduct_star_self_nonneg`: the number $\bar v \cdot v$ is nonnegative and vanishes only at $v = 0$. The lemma `Matrix.dotProduct_star_self_pos_iff` gives the strict form. For matrices, `Matrix.conjTranspose_mul_self_eq_zero` says that $A^* A = 0$ only when $A = 0$, and `Matrix.conjTranspose_mul_self_mulVec_eq_zero` says that $A^* A v = 0$ implies $A v = 0$. These facts are the base of positive semidefinite matrices in Chapter 5. Two more statements separate vectors: `dotProduct_eq` says that $v = w$ when $v \cdot u = w \cdot u$ for all $u$, and `dotProduct_eq_zero_iff` says that $v = 0$ when $v \cdot u = 0$ for all $u$.

#### Vectorization

**Definition (`Matrix.vec`).** For a matrix $A$ with rows indexed by $m$ and columns by $n$, `Matrix.vec A : n × m → R` is the vector of entries with $A.\mathrm{vec}(j, i) = A_{ij}$, so the columns of $A$ are put one after the other.

This is `Matrix.vec_eq_uncurry`. The map is bijective (`Matrix.vec_bijective`) and linear (`Matrix.vec_add`, `Matrix.vec_smul`). The dot product of two vectorizations is a trace: `Matrix.vec_dotProduct_vec` says $\mathrm{vec}(A) \cdot \mathrm{vec}(B) = \operatorname{tr}(A^T B)$, and `Matrix.star_vec_dotProduct_vec` is the version with the conjugate transpose. The main identity links vectorization to the Kronecker product of Section 8.

**Theorem (`Matrix.kronecker_mulVec_vec`).** Over a commutative ring, $(B \otimes A)\, \mathrm{vec}(X) = \mathrm{vec}(A X B^T)$.

*Proof sketch.* Compare the entries at $(l, k)$. The left side is $\sum_{j, i} B_{lj} A_{ki} X_{ij}$. The right side is the entry $(k, l)$ of $A X B^T$, which is $\sum_{i, j} A_{ki} X_{ij} B_{lj}$. The two sums are equal because the ring is commutative. $\square$

Over a noncommutative ring, `Matrix.kronecker_mulVec_vec_of_commute` asks that the entries of $B$ commute with all elements. The identity turns a matrix equation $A X B^T = C$ into a linear system for $\mathrm{vec}(X)$. The lemma `Matrix.vec_hadamard` says that vectorization sends the entrywise product to the entrywise product.

#### Common errors

1. The notation `!![a, b; c, d]` separates rows with `;` and entries with `,`. The notation `![a, b]` is a vector, not a matrix; a column matrix needs `Matrix.replicateCol`.
2. `Matrix.reindex eₘ eₙ M` has the entry `M (eₘ.symm i) (eₙ.symm j)` at $(i, j)$, with the inverse equivalences. A rewrite with the wrong direction of $e$ fails.
3. The vector `Matrix.vec A` is indexed by `n × m`, column index first. It is not indexed by `m × n`.

### Exercises

1. (A) Compute `!![1, 2; 3, 4] * !![0, 1; 1, 0]` with `Matrix.mul_fin_two`, and describe the effect of the second matrix.
2. (A) Show that `(M.updateRow i b) i j = b j` for all $j$.
3. (B) Prove that the dimension of the space of $m \times n$ matrices over a field $K$ is $|m| \cdot |n|$, with `Matrix.stdBasis`.
4. (B) Let $w : n \to K$ have $k$ nonzero entries. Show that the kernel of the diagonal matrix of $w$ has dimension $|n| - k$.
5. (B) Prove that for each real matrix $A$, $\operatorname{tr}(A^T A) \ge 0$, with equality only when $A = 0$. Use `Matrix.vec_dotProduct_vec`.
6. (C) Show that the equation $A X + X B = C$ for square matrices is a linear system for $\mathrm{vec}(X)$ with the matrix $1 \otimes A + B^T \otimes 1$.

### Reference

<?reference?>
