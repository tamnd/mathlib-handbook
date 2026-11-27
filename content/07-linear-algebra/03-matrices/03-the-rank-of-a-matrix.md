---
title: The rank of a matrix and row reduction
kind: theory
modules:
  - Mathlib.LinearAlgebra.Matrix.Rank
explains:
  E3: [Matrix.rank, Matrix.rank_transpose]
  E2: [Matrix.rank_eq_finrank_range_toLin, Matrix.finrank_span_range_col, Matrix.finrank_span_range_row, Matrix.rank_mul_le, Matrix.cRank, Matrix.rank_le_width]
  E1: auto
families: []
requires: [V07.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The rank of a matrix and row reduction

### Overview

The rank of a matrix is the number of its independent columns. It is the dimension of the range of the linear map $x \mapsto A x$, and it decides the solvability of the linear systems with the matrix $A$: by rank-nullity, the solutions of $A x = 0$ form a space of dimension $n - \operatorname{rank} A$. A matrix also has rows, and the number of independent rows is a second rank. A first surprise of linear algebra is that the two numbers are equal, even for a matrix that is far from square.

This section defines the rank over a field, proves that the row rank equals the column rank, proves the bounds for the rank of a product, and describes the computation of the rank by row reduction. The worked examples compute the rank of explicit $3 \times 3$ and $3 \times 4$ matrices, and show that the rank depends on the field.

### Definitions

In this section $K$ is a field and $A$ is an $m \times n$ matrix over $K$. The columns of $A$ are vectors of $K^m$, and the rows are vectors of $K^n$.

**Definition (Column rank and row rank).** The column rank of $A$ is the dimension of the span of its columns in $K^m$. The row rank is the dimension of the span of its rows in $K^n$. The rank $\operatorname{rank} A$ is the column rank.

The span of the columns is the range of the map $T_A : K^n \to K^m$, $x \mapsto A x$, since $A x = \sum_j x_j A_{\cdot j}$ is the combination of the columns with the coefficients $x_j$. So $\operatorname{rank} A = \dim \operatorname{im} T_A$.

::: mathlib
`Matrix.rank` · `Mathlib.LinearAlgebra.Matrix.Rank`

The rank `A.rank : ℕ` of a matrix over a semiring, defined as `A.cRank.toNat`. It needs no finiteness of the index types in the definition. Over a field with finite index types it is the dimension of the span of the columns.

<?decl Matrix.rank?>
:::

::: mathlib
`Matrix.cRank` · `Mathlib.LinearAlgebra.Matrix.Rank`

The rank as a cardinal: `A.cRank = Module.rank R (span R (range A.col))`, where `A.col j` is the column `j`. It covers matrices with infinitely many columns. The rank in `ℕ∞` is `Matrix.eRank`.

<?decl Matrix.cRank?>
:::

::: mathlib
`Matrix.finrank_span_range_col` · `Mathlib.LinearAlgebra.Matrix.Rank`

The rank is the dimension of the span of the columns: `finrank R (span R (range A.col)) = A.rank`.

<?decl Matrix.finrank_span_range_col?>
:::

::: mathlib
`Matrix.rank_eq_finrank_range_toLin` · `Mathlib.LinearAlgebra.Matrix.Rank`

For any bases `v₁` of the target and `v₂` of the source, `A.rank = finrank R (range (toLin v₂ v₁ A))`. So the rank of a matrix is the rank of each linear map that it represents, in any bases.

<?decl Matrix.rank_eq_finrank_range_toLin?>
:::

**Definition (Elementary row operations).** The elementary row operations on a matrix are: swap two rows; multiply a row by a nonzero scalar; add a multiple of one row to another row. Each one is the product on the left with an invertible $m \times m$ matrix, an elementary matrix. For example, adding $c$ times the row $k$ to the row $i$ is the product with $I + c E_{ik}$, whose inverse is $I - c E_{ik}$.

**Definition (Row echelon form).** A matrix is in row echelon form if each nonzero row has its first nonzero entry, the pivot, strictly to the right of the pivot of the row above, and the zero rows are at the bottom.

### Theorems and proofs

**Theorem (Rank of a product).** Let $A$ be $m \times n$ and $B$ be $n \times p$. Then $\operatorname{rank}(A B) \le \min(\operatorname{rank} A, \operatorname{rank} B)$. If $P$ is an invertible $m \times m$ matrix and $Q$ an invertible $n \times n$ matrix, then $\operatorname{rank}(P A Q) = \operatorname{rank} A$.

*Proof.* The map $T_{AB} = T_A \circ T_B$, by Section 2. Its range $T_A(T_B(K^p))$ is contained in $T_A(K^n)$, so $\operatorname{rank}(A B) \le \operatorname{rank} A$. It is also the image of the space $T_B(K^p)$ under the linear map $T_A$, and the image of a space has at most its dimension, by rank-nullity. So $\operatorname{rank}(A B) \le \operatorname{rank} B$. For the second claim, apply the first one twice: $\operatorname{rank}(P A Q) \le \operatorname{rank} A$, and $A = P^{-1} (P A Q) Q^{-1}$ gives the reverse inequality. $\square$

::: mathlib
`Matrix.rank_mul_le` · `Mathlib.LinearAlgebra.Matrix.Rank`

The bound `(A * B).rank ≤ min A.rank B.rank` over a commutative ring with the strong rank condition. The two halves are `Matrix.rank_mul_le_left` and `Matrix.rank_mul_le_right`. The equality for an invertible factor is `Matrix.rank_mul_eq_left_of_isUnit_det` and its mirror.

<?decl Matrix.rank_mul_le?>
:::

**Theorem (Bounds).** $\operatorname{rank} A \le \min(m, n)$.

*Proof.* The span of the columns lies in $K^m$, so its dimension is at most $m$. It is spanned by $n$ vectors, so its dimension is at most $n$ by the Steinitz theorem. $\square$

::: mathlib
`Matrix.rank_le_width` · `Mathlib.LinearAlgebra.Matrix.Rank`

For `A : Matrix (Fin m) (Fin n) R`: `A.rank ≤ n`. The general form for any finite index type is `Matrix.rank_le_card_width`.

<?decl Matrix.rank_le_width?>
:::

**Theorem (Row rank equals column rank).** For each matrix $A$ over a field, the row rank of $A$ equals its column rank. Equivalently, $\operatorname{rank} A^{\mathsf{T}} = \operatorname{rank} A$.

*Proof.* Let $r$ be the column rank of $A$, and let $c_1, \dots, c_r \in K^m$ be a basis of the span of the columns. Each column $A_{\cdot j}$ is a combination $A_{\cdot j} = \sum_{k=1}^r R_{kj} c_k$ with scalars $R_{kj}$. Let $C$ be the $m \times r$ matrix with the columns $c_1, \dots, c_r$, and $R = (R_{kj})$ the $r \times n$ matrix of the coefficients. The column $j$ of $C R$ is $\sum_k R_{kj} c_k = A_{\cdot j}$, so
$$A = C R.$$
Now read this product by rows. The row $i$ of $C R$ is $\sum_{k=1}^r C_{ik} R_{k \cdot}$, a combination of the $r$ rows of $R$. So all the rows of $A$ lie in the span of the $r$ rows of $R$, and the row rank of $A$ is at most $r$.

So the row rank of each matrix is at most its column rank. Apply this to $A^{\mathsf{T}}$, whose rows are the columns of $A$ and whose columns are the rows of $A$: the column rank of $A$ is at most the row rank of $A$. The two inequalities give equality. $\square$

The proof uses only a basis of the column space, so it works over each field. It does not use the determinant.

::: mathlib
`Matrix.rank_transpose` · `Mathlib.LinearAlgebra.Matrix.Rank`

The statement `Aᵀ.rank = A.rank` over a field, for finite index types. The proof in Mathlib is different from the proof above: it identifies the transpose with the dual map of Chapter 6 and uses that a map and its dual have ranges of the same dimension. Mathlib states it for fields.

<?decl Matrix.rank_transpose?>
:::

::: mathlib
`Matrix.finrank_span_range_row` · `Mathlib.LinearAlgebra.Matrix.Rank`

The rank is the dimension of the span of the rows: `finrank R (span R (range A.row)) = A.rank`, over a field. It follows from `rank_transpose`.

<?decl Matrix.finrank_span_range_row?>
:::

**Theorem (Row reduction).** Each matrix over a field can be brought to row echelon form by elementary row operations. The rank of $A$ is the number of the nonzero rows of an echelon form of $A$, that is, the number of pivots.

*Proof.* Existence, by induction on the number of rows. If $A = 0$, it is in echelon form. Otherwise let $j$ be the first column with a nonzero entry. Swap rows to bring a nonzero entry $a$ of this column to the first row. For each other row $i$ with the entry $a_i$ in the column $j$, add $-a_i / a$ times the first row to the row $i$. Now the column $j$ has the only nonzero entry $a$ in the first row, and the columns left of $j$ are zero. Apply the induction to the matrix of the rows $2$ to $m$. Its operations do not touch the first row, and its pivots lie right of $j$.

Rank: each elementary operation is the product on the left with an invertible matrix, so it does not change the rank, by the theorem on products. For a matrix $E$ in echelon form with $r$ nonzero rows, the nonzero rows are independent: in a relation $\sum_i \lambda_i E_{i \cdot} = 0$, look at the column of the pivot of the first row. Only the first row has a nonzero entry there, so $\lambda_1 = 0$. Then look at the pivot of the second row, and so on. So the row rank of $E$ is $r$, and by the last theorem its rank is $r$. $\square$

The row operations change the span of the columns, but they keep the linear relations between the columns: $A x = 0$ if and only if $P A x = 0$ for an invertible $P$. So the columns of $A$ in the positions of the pivots of an echelon form are a basis of the column space of $A$.

### Examples

**Example (Rank of a $3 \times 3$ matrix).** Let
$$A = \begin{pmatrix} 1 & 2 & 3 \\ 4 & 5 & 6 \\ 7 & 8 & 9 \end{pmatrix}$$
over $\mathbb{Q}$. Subtract $4$ times the row $1$ from the row $2$, and $7$ times the row $1$ from the row $3$:
$$\begin{pmatrix} 1 & 2 & 3 \\ 0 & -3 & -6 \\ 0 & -6 & -12 \end{pmatrix}.$$
Subtract $2$ times the row $2$ from the row $3$:
$$\begin{pmatrix} 1 & 2 & 3 \\ 0 & -3 & -6 \\ 0 & 0 & 0 \end{pmatrix}.$$
There are two pivots, in the columns $1$ and $2$. So $\operatorname{rank} A = 2$. The columns $1$ and $2$ of $A$, $(1, 4, 7)$ and $(2, 5, 8)$, are a basis of the column space. The relation between the columns comes from the kernel: the echelon form gives $x_1 + 2x_2 + 3x_3 = 0$ and $-3x_2 - 6x_3 = 0$, so $x_2 = -2x_3$ and $x_1 = x_3$. With $x_3 = 1$: $A_{\cdot 1} - 2A_{\cdot 2} + A_{\cdot 3} = 0$, that is, $(1,4,7) - 2(2,5,8) + (3,6,9) = 0$. The rows obey the same count: $R_1 - 2R_2 + R_3 = (1 - 8 + 7, 2 - 10 + 8, 3 - 12 + 9) = 0$.

**Example (A rank that depends on a parameter).** Let $a \in \mathbb{Q}$ and
$$B_a = \begin{pmatrix} 1 & 1 & a \\ 1 & a & 1 \\ a & 1 & 1 \end{pmatrix}.$$
Subtract the row $1$ from the row $2$, and $a$ times the row $1$ from the row $3$:
$$\begin{pmatrix} 1 & 1 & a \\ 0 & a - 1 & 1 - a \\ 0 & 1 - a & 1 - a^2 \end{pmatrix}.$$
Add the row $2$ to the row $3$. The entry $(3, 3)$ becomes $(1 - a) + (1 - a^2) = (1 - a)(2 + a)$:
$$\begin{pmatrix} 1 & 1 & a \\ 0 & a - 1 & 1 - a \\ 0 & 0 & (1 - a)(2 + a) \end{pmatrix}.$$
If $a = 1$, the rows $2$ and $3$ are zero, and $\operatorname{rank} B_1 = 1$: all three rows of $B_1$ are $(1, 1, 1)$. If $a = -2$, the row $3$ is zero and the row $2$ is $(0, -3, 3)$, so $\operatorname{rank} B_{-2} = 2$. For all other $a$, there are three pivots, and $\operatorname{rank} B_a = 3$.

**Example (The rank depends on the field).** Let
$$C = \begin{pmatrix} 1 & 1 & 0 \\ 0 & 1 & 1 \\ 1 & 0 & 1 \end{pmatrix}.$$
Subtract the row $1$ from the row $3$: the row $3$ becomes $(0, -1, 1)$. Add the row $2$: it becomes $(0, 0, 2)$. Over $\mathbb{Q}$ the entry $2$ is a pivot, and $\operatorname{rank} C = 3$. Over $\mathbb{F}_2$, $2 = 0$, so the last row is zero and $\operatorname{rank} C = 2$. This matches Section 2 of Chapter 2, where the columns of $C$ are independent over $\mathbb{Q}$ and dependent over $\mathbb{F}_2$.

**Example (A $3 \times 4$ matrix and its kernel).** Let
$$D = \begin{pmatrix} 1 & 2 & 0 & 1 \\ 2 & 4 & 1 & 4 \\ 3 & 6 & 1 & 5 \end{pmatrix}.$$
Row 2 minus twice row 1 gives $(0, 0, 1, 2)$. Row 3 minus three times row 1 gives $(0, 0, 1, 2)$. Subtract the new row 2 from the new row 3:
$$\begin{pmatrix} 1 & 2 & 0 & 1 \\ 0 & 0 & 1 & 2 \\ 0 & 0 & 0 & 0 \end{pmatrix}.$$
The pivots are in the columns $1$ and $3$, so $\operatorname{rank} D = 2$. The kernel has dimension $4 - 2 = 2$, with the free unknowns $x_2$ and $x_4$: $x_3 = -2x_4$ and $x_1 = -2x_2 - x_4$. A basis of the kernel is $(-2, 1, 0, 0)$ and $(-1, 0, -2, 1)$.

**Counterexample (Rank of a product).** The inequality $\operatorname{rank}(A B) \le \min$ can be strict. Let $A = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and $B = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$. Both have rank $1$, and $A B = 0$ has rank $0$. The rank is also not additive: $\operatorname{rank}(A + B) = 2 = 1 + 1$, but $\operatorname{rank}(A + (-A)) = 0 < 1 + 1$.

### The library around it

The rank and its properties are in `Mathlib.LinearAlgebra.Matrix.Rank`. The lemma `Matrix.rank_mul_ge` gives the inequality of Sylvester, $\operatorname{rank} A + \operatorname{rank} B \le \operatorname{rank}(A B) + n$, over a domain. The lemmas `Matrix.rank_transpose_mul_self` and `Matrix.rank_conjTranspose_mul_self` say that $A^{\mathsf{T}} A$ has the rank of $A$ over an ordered field, and that $A^{*} A$ has the rank of $A$ over a star-ordered field such as $\mathbb{C}$. Row reduction is in `Mathlib.LinearAlgebra.Matrix.Transvection`. The theorem `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec` writes each square matrix over a field as $L D L'$, with $L$ and $L'$ products of transvections and $D$ diagonal.

### Exercises

1. (A) Compute the rank of $\begin{pmatrix} 2 & 4 & 6 \\ 1 & 2 & 3 \\ 0 & 1 & 1 \end{pmatrix}$ over $\mathbb{Q}$.
2. (A) Compute the rank of $\begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$ over $\mathbb{Q}$, over $\mathbb{F}_2$ and over $\mathbb{F}_3$. Hint: the entry that decides is $4 - 6 = -2$.
3. (A) Show that a matrix of rank $1$ is a product $u v^{\mathsf{T}}$ of a column and a row.
4. (B) For which $t \in \mathbb{R}$ does the system $x + y + t z = 1$, $x + t y + z = 1$, $t x + y + z = 1$ have exactly one solution, no solution, or infinitely many? Hint: use the example $B_t$ and compare the rank of $B_t$ with the rank of the matrix with the column $(1, 1, 1)$ added.
5. (B) Show that $\operatorname{rank}(A + B) \le \operatorname{rank} A + \operatorname{rank} B$. Hint: the column space of $A + B$ lies in the sum of the column spaces.
6. (B) Let $A$ be $m \times n$ of rank $r$. Show that there are invertible $P$ and $Q$ with $P A Q = \begin{pmatrix} I_r & 0 \\ 0 & 0 \end{pmatrix}$. Hint: row reduce, then reduce the columns.
7. (B) Show that an $n \times n$ matrix with $A^2 = 0$ has rank at most $n/2$. Hint: the column space of $A$ lies in the kernel of $A$.
8. (C) Prove the inequality of Sylvester: $\operatorname{rank} A + \operatorname{rank} B \le \operatorname{rank}(A B) + n$ for $A$ of size $m \times n$ and $B$ of size $n \times p$. Hint: apply rank-nullity to $T_A$ restricted to the range of $T_B$.

### Notes and history

The notion of the rank of a matrix is due to Frobenius in 1879, who defined it through the largest nonzero minor. Sylvester proved his inequality in 1884. The method of row reduction is much older: it is in the Chinese text "Nine Chapters on the Mathematical Art", from about the second century BCE, and it bears the name of Gauss, who used it for least squares problems in the early nineteenth century. The proof that the row rank equals the column rank through the factorization $A = C R$ is standard in modern texts.

The definition as the rank of the column space works over each semiring, and the theorems specialize to fields with their hypotheses. The proof of `rank_transpose` through the dual map is an example of a choice in Mathlib: reuse a general theorem on linear maps, rather than repeat a matrix computation.

### Reference

<?reference?>
