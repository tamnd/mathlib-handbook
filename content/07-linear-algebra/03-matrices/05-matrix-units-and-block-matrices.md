---
title: Matrix units and block matrices
kind: api
modules:
  - Mathlib.Data.Matrix.Basis
  - Mathlib.Data.Matrix.Block
  - Mathlib.Data.Matrix.ColumnRowPartitioned
  - Mathlib.Data.Matrix.Composition
explains:
  E2: [Matrix.single, Matrix.single_mul_single_same, Matrix.matrix_eq_sum_single, Matrix.center_eq_scalar_image, Matrix.fromBlocks, Matrix.fromBlocks_multiply, Matrix.blockDiagonal_mul, Matrix.fromCols_mul_fromRows, Matrix.compRingEquiv]
  E1: auto
families: []
requires: [V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Matrix units and block matrices

### Overview

There are two standard ways to take a matrix apart. The first writes it as a sum of matrix units: the matrix $E_{ij}$ has the entry $1$ at $(i, j)$ and $0$ elsewhere, and each matrix is $\sum_{i,j} a_{ij} E_{ij}$. The second cuts it into blocks: a matrix indexed by $(n \oplus o) \times (l \oplus m)$ has four blocks, and the product of two such matrices is computed block by block like a $2 \times 2$ product. This section gives the Mathlib form of both. It also covers matrices with block diagonal form, the partition of a matrix into columns or rows, and the identification of a matrix of matrices with one large matrix.

### The library around it

#### Matrix units

The matrix `Matrix.single i j c` has the entry $c$ at $(i, j)$ and $0$ elsewhere. The value is `Matrix.single_apply`, with the special cases `Matrix.single_apply_same` and `Matrix.single_apply_of_ne`. It is additive in $c$, so it is the additive map `Matrix.singleAddMonoidHom i j` and the linear map `Matrix.singleLinearMap R i j`.

**Theorem.** Each matrix is the sum of its entries times the matrix units: $M = \sum_{i,j} E_{ij}(M_{ij})$.

*Proof.* At the position $(k, l)$, the term $E_{ij}(M_{ij})$ is $M_{ij}$ when $(i, j) = (k, l)$ and $0$ otherwise. So the sum is $M_{kl}$. $\square$

This is `Matrix.matrix_eq_sum_single`. It gives the induction principle `Matrix.induction_on`: a property that holds for $0$, for each matrix unit, and for sums holds for each matrix. It also gives the extensionality lemmas `Matrix.ext_addMonoidHom` and `Matrix.ext_linearMap`: two linear maps out of a space of matrices are equal if they agree on each matrix unit. The universal property is `Matrix.liftLinear`, which builds a linear map out of matrices from a family of linear maps on the entries.

**Theorem.** $E_{ij}(c) E_{jk}(d) = E_{ik}(c d)$, and $E_{ij}(c) E_{lk}(d) = 0$ for $j \ne l$.

*Proof.* The entry $(a, b)$ of the product is $\sum_x E_{ij}(c)_{ax} E_{lk}(d)_{xb}$. A term can be nonzero only for $a = i$, $x = j$, $x = l$ and $b = k$. So the product is $0$ for $j \ne l$, and for $j = l$ it has the single entry $c d$ at $(i, k)$. $\square$

These are `Matrix.single_mul_single_same` and `Matrix.single_mul_single_of_ne`. The general form `Matrix.single_mul_mul_single` says that $E_{ii'}(a) X E_{j'j}(b) = E_{ij}(a X_{i'j'} b)$: a product with matrix units on both sides picks out one entry. The products with a matrix pick a row or a column: `Matrix.single_mul_apply_same` and `Matrix.mul_single_apply_same`. Other rules are `Matrix.transpose_single`, `Matrix.map_single`, `Matrix.smul_single`, `Matrix.sum_single_eq_diagonal` and `Matrix.sum_single_one`, which says that $\sum_i E_{ii} = I$.

#### The center of a matrix ring

**Theorem.** The center of $\operatorname{Mat}_n(\alpha)$ is the set of scalar matrices $r I$ with $r$ in the center of $\alpha$.

*Proof.* A scalar matrix with a central scalar commutes with each matrix by Section 4. Conversely, let $M$ commute with each $E_{ij}(1)$. For $k \ne i$, the entry $(k, j)$ of $E_{ij}(1) M = M E_{ij}(1)$ gives $M_{ki} = 0$, so $M$ is diagonal. The entry $(i, j)$ gives $M_{jj} = M_{ii}$, so all diagonal entries are equal to one $r$. Finally $M$ commutes with $E_{ii}(s)$ for each $s$, which gives $r s = s r$. $\square$

This is `Matrix.center_eq_scalar_image`. The steps are the lemmas `Matrix.col_eq_zero_of_commute_single`, `Matrix.row_eq_zero_of_commute_single`, `Matrix.diag_eq_of_commute_single` and `Matrix.mem_range_scalar_of_commute_single`. Over a commutative ring the result is `Matrix.center_eq_range`, and the forms for the centers as substructures are `Matrix.subsemiringCenter_eq_scalar_map` and `Matrix.subringCenter_eq_scalar_map`.

#### Block matrices

For matrices $A : n \times l$, $B : n \times m$, $C : o \times l$ and $D : o \times m$, the block matrix `Matrix.fromBlocks A B C D` is indexed by $(n \oplus o) \times (l \oplus m)$:
$$\begin{pmatrix} A & B \\ C & D \end{pmatrix}.$$
The inverse operations are `Matrix.toBlocks₁₁`, `Matrix.toBlocks₁₂`, `Matrix.toBlocks₂₁` and `Matrix.toBlocks₂₂`, with `Matrix.fromBlocks_toBlocks` and `Matrix.toBlocks_fromBlocks₁₁`. Two block matrices are equal if and only if their four blocks are (`Matrix.fromBlocks_inj`).

**Theorem.** The product of block matrices is computed block by block:
$$\begin{pmatrix} A & B \\ C & D \end{pmatrix} \begin{pmatrix} A' & B' \\ C' & D' \end{pmatrix} = \begin{pmatrix} A A' + B C' & A B' + B D' \\ C A' + D C' & C B' + D D' \end{pmatrix}.$$

*Proof.* The sum over $l \oplus m$ in the product splits into a sum over $l$ and a sum over $m$. On each block of rows and columns, the first sum is the product of the blocks of index $l$ and the second sum is the product of the blocks of index $m$. $\square$

This is `Matrix.fromBlocks_multiply`. The same rules hold for the other operations: `Matrix.fromBlocks_add`, `Matrix.fromBlocks_smul`, `Matrix.fromBlocks_transpose`, `Matrix.fromBlocks_map`, `Matrix.fromBlocks_mulVec` and `Matrix.fromBlocks_one`. The identity is `fromBlocks 1 0 0 1`. For block diagonal matrices, `Matrix.fromBlocks_diagonal_pow` computes the powers. The predicate `Matrix.IsTwoBlockDiagonal` says that the two off diagonal blocks vanish. The determinant of a block triangular matrix is the product of the determinants of its diagonal blocks; this is in Chapter 4.

A general square matrix can be cut along a predicate: `Matrix.toBlock M p q` is the submatrix on the rows with $p$ and the columns with $q$. The lemma `Matrix.toBlock_mul_eq_add` splits a product along $q$ and its negation. For a map $b : m \to \beta$, `Matrix.toSquareBlock M b k` is the square block of the indices with $b(i) = k$.

#### Block diagonal matrices

A family of matrices $M_k : m \times n$ indexed by $k \in o$ gives the block diagonal matrix `Matrix.blockDiagonal M` indexed by $(m \times o) \times (n \times o)$, with the block $M_k$ on the diagonal at the position $k$ and $0$ elsewhere. The entries are `Matrix.blockDiagonal_apply_eq` and `Matrix.blockDiagonal_apply_ne`.

**Theorem.** The product of two block diagonal matrices is block diagonal, with the products of the blocks: $\operatorname{diag}(M_k) \operatorname{diag}(N_k) = \operatorname{diag}(M_k N_k)$.

*Proof.* The entry $((i, k), (j, k'))$ of the product is $\sum_{(x, k'')} \operatorname{diag}(M)_{(i,k),(x,k'')} \operatorname{diag}(N)_{(x,k''),(j,k')}$. A term is nonzero only if $k'' = k$ and $k' = k''$. So the entry is $0$ for $k \ne k'$, and it is $(M_k N_k)_{ij}$ for $k = k'$. $\square$

This is `Matrix.blockDiagonal_mul`. The square version is the ring map `Matrix.blockDiagonalRingHom`. The other rules are `Matrix.blockDiagonal_pow`, `Matrix.blockDiagonal_transpose`, `Matrix.blockDiagonal_diagonal` and `Matrix.blockDiagonal_injective`. The inverse operation `Matrix.blockDiag M k` extracts the block $k$ of the diagonal, and `Matrix.blockDiag_blockDiagonal` says that it is a left inverse. The primed forms `Matrix.blockDiagonal'` and `Matrix.blockDiag'` allow blocks of different sizes, indexed by a sigma type, and `Matrix.blockDiagonal'_eq_blockDiagonal` relates the two.

#### Columns and rows

A matrix with the columns indexed by $n_1 \oplus n_2$ is a pair of matrices placed side by side. This is `Matrix.fromCols A₁ A₂`, with the parts `Matrix.toCols₁` and `Matrix.toCols₂`. The matrix with the rows indexed by $m_1 \oplus m_2$ is `Matrix.fromRows A₁ A₂`, with `Matrix.toRows₁` and `Matrix.toRows₂`. The constructions are injective (`Matrix.fromCols_inj`), and `Matrix.fromRows_fromCols_eq_fromBlocks` says that a block matrix is a matrix of rows of columns.

**Theorem.** $\begin{pmatrix} A_1 & A_2 \end{pmatrix} \begin{pmatrix} B_1 \\ B_2 \end{pmatrix} = A_1 B_1 + A_2 B_2$.

*Proof.* The sum over $n_1 \oplus n_2$ splits into a sum over $n_1$, which gives $A_1 B_1$, and a sum over $n_2$, which gives $A_2 B_2$. $\square$

This is `Matrix.fromCols_mul_fromRows`. The opposite product is a block matrix, `Matrix.fromRows_mul_fromCols`. The products with one matrix are `Matrix.mul_fromCols` and `Matrix.fromRows_mul`, and the products with vectors are `Matrix.fromCols_mulVec` and `Matrix.vecMul_fromRows`. The transpose exchanges columns and rows: `Matrix.transpose_fromCols`. For square results, `Matrix.fromCols_mul_fromRows_eq_one_comm` says that a left inverse of this form is a right inverse.

#### Matrices of matrices

A matrix whose entries are matrices is one large matrix. For $M : I \times J$ with entries in `Matrix K L R`, the equivalence `Matrix.comp I J K L R` gives the matrix indexed by $(I \times K) \times (J \times L)$ with the entry $M_{ij}$ at $(k, l)$ at the position $((i, k), (j, l))$ (`Matrix.comp_apply`). The structured versions are `Matrix.compAddEquiv`, `Matrix.compLinearEquiv`, the ring isomorphism `Matrix.compRingEquiv` for square matrices, and the algebra isomorphism `Matrix.compAlgEquiv`. So $\operatorname{Mat}_I(\operatorname{Mat}_J(R)) \simeq \operatorname{Mat}_{I \times J}(R)$ as rings. The rules are `Matrix.comp_single_single`, `Matrix.comp_diagonal_diagonal`, `Matrix.transpose_comp` and `Matrix.isUnit_comp_iff`.

#### Common errors

1. Expecting `Matrix.single_mul_single_same` to rewrite $E_{ij}(c) E_{lk}(d)$ when $j$ and $l$ are different variables. The lemma needs the same middle index. Split into the cases $j = l$ and $j \ne l$, and use `Matrix.single_mul_single_of_ne` in the second case.
2. Expecting `Matrix.fromBlocks` to accept blocks of any sizes. The index types are fixed by the blocks: $A$ and $B$ share the rows $n$, and $A$ and $C$ share the columns $l$. A mismatch gives a type error, not a false statement.
3. Confusing `Matrix.blockDiagonal`, indexed by $m \times o$ with equal block sizes, and `Matrix.blockDiagonal'`, indexed by a sigma type. Lemmas about one do not apply to the other without `Matrix.blockDiagonal'_eq_blockDiagonal`.

### Exercises

1. (A) Write $\begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$ as a sum of matrix units, and compute $E_{12} E_{21}$ and $E_{21} E_{12}$.
2. (A) Use `Matrix.fromBlocks_multiply` to compute the square of $\begin{pmatrix} I & B \\ 0 & I \end{pmatrix}$ and its $k$-th power.
3. (B) Show that $\begin{pmatrix} A & 0 \\ 0 & D \end{pmatrix}$ is invertible if and only if $A$ and $D$ are invertible.
4. (B) Show that the only two sided ideals of $\operatorname{Mat}_2(K)$ for a field $K$ are $0$ and the whole ring. Hint: use `Matrix.single_mul_mul_single`.
5. (B) Let $A_1, A_2$ be $n \times n$ matrices. Show that $\begin{pmatrix} A_1 & A_2 \end{pmatrix} \begin{pmatrix} A_1^T \\ A_2^T \end{pmatrix} = A_1 A_1^T + A_2 A_2^T$.
6. (C) Use `Matrix.compRingEquiv` to show that the ring $\operatorname{Mat}_2(\operatorname{Mat}_3(R))$ is isomorphic to $\operatorname{Mat}_6(R)$, and describe the image of $E_{12}(E_{23}(1))$.

### Reference

<?reference?>
