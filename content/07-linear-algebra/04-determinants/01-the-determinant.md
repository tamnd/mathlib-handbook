---
title: The determinant and its properties
kind: theory
modules:
  - Mathlib.LinearAlgebra.Matrix.Determinant.Basic
  - Mathlib.LinearAlgebra.Matrix.Block
explains:
  E3: [Matrix.det, Matrix.det_transpose]
  E2: [Matrix.det_apply, Matrix.detRowAlternating, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_zero_of_row_eq, Matrix.det_succ_row_zero, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.det_smul, Matrix.det_of_isUpperTriangular, Matrix.det_updateRow_add_smul_self, Matrix.det_fromBlocks_zero₂₁]
  E1: auto
families: []
requires: [V07.C03, V05.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The determinant and its properties

### Overview

The determinant of a square matrix is a polynomial in its entries. For a $2 \times 2$ matrix it is $a d - b c$, and for an $n \times n$ matrix it is a sum of $n!$ products, one for each permutation of the indices. This formula is hard to compute with directly, but it has a short list of properties that determine it: it is linear in each row, it is zero when two rows are equal, and it is $1$ on the identity matrix. Each computation in practice uses these properties, through row reduction or through the expansion along a row.

This section works over a commutative ring $R$. It defines the determinant by the formula of Leibniz, proves that it is multilinear and alternating in the rows, proves that the transpose does not change it, and proves the Laplace expansion along the first row. The examples compute determinants of explicit $2 \times 2$, $3 \times 3$ and $4 \times 4$ matrices, and of triangular and block matrices.

### Definitions

Let $n$ be a finite index type, usually $\{1, \dots, n\}$, and let $S_n$ be the group of the permutations of $n$. Each permutation $\sigma$ has a sign $\operatorname{sgn} \sigma \in \{1, -1\}$, which is a group homomorphism and is $-1$ on each transposition (Volume 5, Chapter 7).

**Definition (Determinant).** The determinant of a square matrix $M$ over $R$ is
$$\det M = \sum_{\sigma \in S_n} \operatorname{sgn} \sigma \prod_{i} M_{\sigma(i), i}.$$

Each term picks one entry from each column $i$, in the row $\sigma(i)$. Since $\sigma$ is a bijection, the term also picks one entry from each row. For $n = 2$ there are two permutations: the identity gives $M_{11} M_{22}$ and the swap gives $-M_{21} M_{12}$. So $\det M = M_{11} M_{22} - M_{12} M_{21}$.

::: mathlib
`Matrix.det` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The determinant `M.det` of a matrix `M : Matrix n n R`, for a commutative ring `R` and a finite type `n` with decidable equality. It is defined as `detRowAlternating M`, the value of an alternating map on the rows. The notation `M.det` is the common form.

<?decl Matrix.det?>
:::

::: mathlib
`Matrix.det_apply` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The formula of Leibniz: `M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i`. The sign is a unit of `ℤ`, and `•` is its action on `R`. The variant `Matrix.det_apply'` writes the sign as an element of `R`.

<?decl Matrix.det_apply?>
:::

**Definition (Multilinear and alternating).** A function $D$ of $n$ vectors $v_1, \dots, v_n \in R^n$ with values in $R$ is multilinear if it is linear in each $v_i$ when the other vectors are fixed. It is alternating if $D(v_1, \dots, v_n) = 0$ whenever $v_i = v_j$ for some $i \neq j$.

::: mathlib
`Matrix.detRowAlternating` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The determinant as an alternating multilinear map `(n → R) [⋀^n]→ₗ[R] R` of the rows of a matrix. A matrix `M` is a function `n → (n → R)` from the row index to the rows, so `detRowAlternating M` makes sense. The general theory of alternating maps is in `Mathlib.LinearAlgebra.Alternating.Basic`.

<?decl Matrix.detRowAlternating?>
:::

For a matrix $M$ and a vector $b$, the matrix $M[i := b]$ is $M$ with the row $i$ replaced by $b$. In Mathlib it is `M.updateRow i b`, and `M.updateCol j b` replaces a column.

### Theorems and proofs

**Theorem (Transpose).** $\det M^{\mathsf{T}} = \det M$.

*Proof.* By definition, $\det M^{\mathsf{T}} = \sum_\sigma \operatorname{sgn} \sigma \prod_i M_{i, \sigma(i)}$. In the product, substitute $i = \sigma^{-1}(k)$. As $i$ runs over $n$, so does $k$, and the product becomes $\prod_k M_{\sigma^{-1}(k), k}$. Also $\operatorname{sgn} \sigma = \operatorname{sgn} \sigma^{-1}$, since $\operatorname{sgn} \sigma \cdot \operatorname{sgn} \sigma^{-1} = \operatorname{sgn} 1 = 1$ and both factors are $\pm 1$. So
$$\det M^{\mathsf{T}} = \sum_\sigma \operatorname{sgn} \sigma^{-1} \prod_k M_{\sigma^{-1}(k), k}.$$
The map $\sigma \mapsto \sigma^{-1}$ is a bijection of $S_n$, so this sum is $\det M$. $\square$

::: mathlib
`Matrix.det_transpose` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The statement `Mᵀ.det = M.det`. It lets each statement on rows give the same statement on columns. For example, the expansion along the first column follows from the expansion along the first row.

<?decl Matrix.det_transpose?>
:::

**Theorem (Multilinearity in the rows).** For each row $i$, vectors $u, v$ and a scalar $c$:
$$\det M[i := u + v] = \det M[i := u] + \det M[i := v], \qquad \det M[i := c u] = c \det M[i := u].$$

*Proof.* In each term $\operatorname{sgn} \sigma \prod_k M_{\sigma(k), k}$, exactly one factor comes from the row $i$: the factor with $\sigma(k) = i$, that is, $k = \sigma^{-1}(i)$. So each term is linear in the row $i$, and so is the sum. $\square$

::: mathlib
`Matrix.det_updateRow_add` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

Additivity in a row: `(updateRow M j (u + v)).det = (updateRow M j u).det + (updateRow M j v).det`. The column form is `Matrix.det_updateCol_add`.

<?decl Matrix.det_updateRow_add?>
:::

::: mathlib
`Matrix.det_updateRow_smul` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

Homogeneity in a row: `(updateRow M j (s • u)).det = s * (updateRow M j u).det`. The column form is `Matrix.det_updateCol_smul`.

<?decl Matrix.det_updateRow_smul?>
:::

**Theorem (Alternating).** If two rows of $M$ are equal, then $\det M = 0$.

*Proof.* Suppose that the rows $i \neq j$ are equal, and let $\tau$ be the transposition of $i$ and $j$. Then $M_{\tau(a), b} = M_{a, b}$ for all $a, b$, since $\tau$ only swaps the two equal rows. The map $\sigma \mapsto \tau \sigma$ is a bijection of $S_n$ without fixed points, so it splits $S_n$ into pairs $\{\sigma, \tau \sigma\}$. In a pair,
$$\prod_k M_{\tau \sigma(k), k} = \prod_k M_{\sigma(k), k}, \qquad \operatorname{sgn}(\tau \sigma) = -\operatorname{sgn} \sigma.$$
So the two terms of a pair cancel, and the sum is $0$. $\square$

This proof works over each commutative ring, also over $\mathbb{F}_2$, where $-1 = 1$. The naive proof "swap the two rows, so $\det M = -\det M$, so $2 \det M = 0$" fails over $\mathbb{F}_2$. The pairing of the permutations avoids the division by $2$.

::: mathlib
`Matrix.det_zero_of_row_eq` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

For `i ≠ j` with `M i = M j`: `M.det = 0`. The column form is `Matrix.det_zero_of_column_eq`.

<?decl Matrix.det_zero_of_row_eq?>
:::

**Corollary (Row operations).** Let $M$ be a square matrix.

1. Swapping two rows multiplies $\det M$ by $-1$. More generally, permuting the rows by $\sigma$ multiplies $\det M$ by $\operatorname{sgn} \sigma$.
2. Multiplying a row by $c$ multiplies $\det M$ by $c$.
3. Adding $c$ times the row $j$ to the row $i \neq j$ does not change $\det M$.
4. If a row of $M$ is zero, then $\det M = 0$.

*Proof.* Part 2 is homogeneity. For part 3, by additivity $\det M[i := M_i + c M_j] = \det M + c \det M[i := M_j]$, and the last matrix has two equal rows, the rows $i$ and $j$. Part 4: a zero row is $0$ times itself, so $\det M = 0 \cdot \det M = 0$. For part 1 with a transposition of the rows $i$ and $j$, let $D(x, y)$ be the determinant of $M$ with the row $i$ replaced by $x$ and the row $j$ by $y$. By the alternating property and multilinearity,
$$0 = D(x + y, x + y) = D(x, x) + D(x, y) + D(y, x) + D(y, y) = D(x, y) + D(y, x).$$
So $D(y, x) = -D(x, y)$. For a general $\sigma$, the substitution $\sigma' = \sigma^{-1} \rho$ in the formula of Leibniz gives the factor $\operatorname{sgn} \sigma$ directly. $\square$

::: mathlib
`Matrix.det_updateRow_add_smul_self` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

Part 3 of the corollary: for `i ≠ j`, `(updateRow A i (A i + c • A j)).det = A.det`. The column form is `Matrix.det_updateCol_add_smul_self`.

<?decl Matrix.det_updateRow_add_smul_self?>
:::

**Theorem (Triangular matrices).** If $M$ is upper triangular, that is, $M_{ij} = 0$ for $i > j$, then $\det M = \prod_i M_{ii}$. The same holds for a lower triangular and for a diagonal matrix.

*Proof.* Take a term $\prod_k M_{\sigma(k), k}$ that is not zero. Then $\sigma(k) \le k$ for all $k$. Then $\sigma(1) \le 1$, so $\sigma(1) = 1$. Next $\sigma(2) \le 2$ and $\sigma(2) \neq \sigma(1) = 1$, so $\sigma(2) = 2$. By induction $\sigma(k) = k$ for each $k$. So only the identity gives a nonzero term, and it is $\prod_i M_{ii}$. For a lower triangular matrix, apply the result to the transpose. $\square$

::: mathlib
`Matrix.det_of_isUpperTriangular` · `Mathlib.LinearAlgebra.Matrix.Block`

For `M.IsUpperTriangular` over a linearly ordered index type: `M.det = ∏ i, M i i`. The lower form is `Matrix.det_of_isLowerTriangular`. Both follow from the general theorem `Matrix.BlockTriangular.det` on block triangular matrices.

<?decl Matrix.det_of_isUpperTriangular?>
:::

::: mathlib
`Matrix.det_smul` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The scalar multiple: `(c • A).det = c ^ Fintype.card n * A.det`. Each of the `n` rows contributes a factor `c`. A common error is to expect `c * A.det`.

<?decl Matrix.det_smul?>
:::

**Theorem (Laplace expansion along the first row).** For an $(n+1) \times (n+1)$ matrix $A$ with the indices $0, \dots, n$, let $A^{(0,j)}$ be the $n \times n$ matrix obtained by the deletion of the row $0$ and the column $j$. Then
$$\det A = \sum_{j=0}^{n} (-1)^j A_{0j} \det A^{(0,j)}.$$

*Proof.* Write the row $0$ as $\sum_j A_{0j} e_j$, where $e_j$ is the standard basis vector. By multilinearity in the row $0$, $\det A = \sum_j A_{0j} \det A[0 := e_j]$. Fix $j$. In the matrix $A[0 := e_j]$, subtract $A_{ij}$ times the row $0$ from each row $i \ge 1$. This does not change the determinant, and it makes the column $j$ equal to $e_0$. Now move the column $j$ to the position $0$ by $j$ swaps of adjacent columns. Each swap gives a factor $-1$, by the column form of the corollary. The result is the block matrix $\begin{pmatrix} 1 & 0 \\ 0 & A^{(0,j)} \end{pmatrix}$, since the row $0$ is now $e_0$ and the column $0$ is $e_0$. In the formula of Leibniz for this block matrix, a term with $\sigma(0) \neq 0$ contains a factor $0$ from the column $0$. The permutations with $\sigma(0) = 0$ are the permutations of $\{1, \dots, n\}$, with the same sign. So the determinant of the block matrix is $\det A^{(0,j)}$. Together, $\det A[0 := e_j] = (-1)^j \det A^{(0,j)}$. $\square$

By the transpose theorem, the same formula holds along the first column. By a permutation of the rows, it holds along each row $i$ with the sign $(-1)^{i+j}$.

::: mathlib
`Matrix.det_succ_row_zero` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The expansion along the row `0` of a matrix indexed by `Fin n.succ`: `A.det = ∑ j, (-1) ^ (j : ℕ) * A 0 j * (A.submatrix Fin.succ j.succAbove).det`. The map `j.succAbove : Fin n → Fin n.succ` skips the value `j`, so the submatrix deletes the row `0` and the column `j`. The expansion along a general row is `Matrix.det_succ_row`.

<?decl Matrix.det_succ_row_zero?>
:::

::: mathlib
`Matrix.det_fin_two` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The formula `A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0` for `A : Matrix (Fin 2) (Fin 2) R`. A proof with a concrete matrix often starts with `rw [Matrix.det_fin_two]` or `simp [Matrix.det_fin_two]`.

<?decl Matrix.det_fin_two?>
:::

::: mathlib
`Matrix.det_fin_three` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The rule of Sarrus as a theorem: the determinant of a `Matrix (Fin 3) (Fin 3) R` is the sum of six signed products of three entries.

<?decl Matrix.det_fin_three?>
:::

**Theorem (Block triangular matrices).** For square matrices $A$ and $D$ and a matrix $B$ of the right size,
$$\det \begin{pmatrix} A & B \\ 0 & D \end{pmatrix} = \det A \det D.$$

*Proof.* Let the blocks have the sizes $p$ and $q$. In a nonzero term of the formula of Leibniz, $\sigma$ maps each column $k \le p$ to a row $\sigma(k) \le p$, since the lower left block is zero. So $\sigma$ maps $\{1, \dots, p\}$ into itself, hence onto itself, and so it also maps $\{p+1, \dots, p+q\}$ onto itself. Such a $\sigma$ is a pair $(\alpha, \beta)$ of permutations of the two blocks, with $\operatorname{sgn} \sigma = \operatorname{sgn} \alpha \operatorname{sgn} \beta$. The term of $\sigma$ is the product of the term of $\alpha$ for $A$ and the term of $\beta$ for $D$. The sum over all pairs factors as $\det A \cdot \det D$. $\square$

::: mathlib
`Matrix.det_fromBlocks_zero₂₁` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The statement `(fromBlocks A B 0 D).det = A.det * D.det`. The block matrix `fromBlocks A B C D` has the index type `m ⊕ n`. The lower triangular form is `Matrix.det_fromBlocks_zero₁₂`.

<?decl Matrix.det_fromBlocks_zero₂₁?>
:::

### Examples

**Example (A $3 \times 3$ determinant by the expansion).** Let
$$A = \begin{pmatrix} 2 & 1 & 3 \\ 0 & -1 & 4 \\ 1 & 2 & 0 \end{pmatrix}.$$
Expand along the first row:
$$\det A = 2 \det \begin{pmatrix} -1 & 4 \\ 2 & 0 \end{pmatrix} - 1 \det \begin{pmatrix} 0 & 4 \\ 1 & 0 \end{pmatrix} + 3 \det \begin{pmatrix} 0 & -1 \\ 1 & 2 \end{pmatrix} = 2(0 - 8) - (0 - 4) + 3(0 + 1) = -16 + 4 + 3 = -9.$$
The rule of Sarrus gives the same value: $2 \cdot (-1) \cdot 0 + 1 \cdot 4 \cdot 1 + 3 \cdot 0 \cdot 2 - 3 \cdot (-1) \cdot 1 - 2 \cdot 4 \cdot 2 - 1 \cdot 0 \cdot 0 = 0 + 4 + 0 + 3 - 16 - 0 = -9$.

**Example (The same determinant by row reduction).** Swap the rows $1$ and $3$ of $A$, which gives a factor $-1$:
$$\begin{pmatrix} 1 & 2 & 0 \\ 0 & -1 & 4 \\ 2 & 1 & 3 \end{pmatrix}.$$
Subtract twice the row $1$ from the row $3$: the row $3$ becomes $(0, -3, 3)$. Subtract three times the row $2$ from the row $3$: it becomes $(0, 0, -9)$. The matrix is now upper triangular with the diagonal $1, -1, -9$, and its determinant is $9$. With the factor of the swap, $\det A = -9$. Row reduction needs about $n^3/3$ operations, and the formula of Leibniz needs about $n \cdot n!$, so for large $n$ only row reduction is practical.

**Example (The matrices with a parameter).** For the matrix $B_a$ of Section 3 of Chapter 3,
$$\det \begin{pmatrix} 1 & 1 & a \\ 1 & a & 1 \\ a & 1 & 1 \end{pmatrix} = 1 \cdot (a - 1) - 1 \cdot (1 - a) + a \cdot (1 - a^2) = 2(a - 1) - a(a - 1)(a + 1).$$
Factor out $a - 1$: $\det B_a = (a - 1)(2 - a^2 - a) = -(a - 1)^2 (a + 2)$. The determinant is zero exactly for $a = 1$ and $a = -2$, which are the two values where the rank is less than $3$.

**Example (A $4 \times 4$ block matrix).** Let
$$M = \begin{pmatrix} 1 & 2 & 5 & 7 \\ 3 & 4 & 6 & 8 \\ 0 & 0 & 2 & 1 \\ 0 & 0 & 1 & 1 \end{pmatrix}.$$
It is block upper triangular with $A = \begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$ and $D = \begin{pmatrix} 2 & 1 \\ 1 & 1 \end{pmatrix}$. So $\det M = \det A \det D = (4 - 6)(2 - 1) = -2$. The upper right block has no effect.

**Counterexample (The determinant is not additive).** For $A = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and $B = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$, $\det A = \det B = 0$, but $A + B = I$ and $\det(A + B) = 1$. The determinant is linear in each row separately, not in the whole matrix.

### The library around it

The determinant is in `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, and the results on block triangular matrices are in `Mathlib.LinearAlgebra.Matrix.Block`. Other files compute special determinants: `Mathlib.LinearAlgebra.Vandermonde` for the Vandermonde matrix (Section 3), `Mathlib.LinearAlgebra.Matrix.SchurComplement` for the determinant of a $2 \times 2$ block matrix with an invertible block, and `Mathlib.LinearAlgebra.Matrix.Permutation` for the matrix of a permutation.

### Exercises

1. (A) Compute $\det \begin{pmatrix} 3 & 0 & 2 \\ 1 & 4 & -1 \\ 2 & 1 & 1 \end{pmatrix}$ by the expansion along the second column and by row reduction.
2. (A) Show that $\det(-A) = (-1)^n \det A$ for an $n \times n$ matrix. Hint: use the theorem on the scalar multiple.
3. (A) Show that an $n \times n$ matrix with $n$ odd and $A^{\mathsf{T}} = -A$ has $\det A = 0$ over $\mathbb{Q}$. Find a counterexample over $\mathbb{F}_2$. Hint: over $\mathbb{F}_2$, $-A = A$.
4. (B) Compute the determinant of the $n \times n$ matrix with $2$ on the diagonal, $-1$ on the two neighbouring diagonals and $0$ elsewhere. Hint: expand along the first row, find a recurrence $d_n = 2 d_{n-1} - d_{n-2}$, and show $d_n = n + 1$.
5. (B) Compute $\det \begin{pmatrix} x & 1 & 1 \\ 1 & x & 1 \\ 1 & 1 & x \end{pmatrix}$ and factor it. Hint: add all the rows to the first row.
6. (B) Show that a function $D$ of the rows of an $n \times n$ matrix that is multilinear and alternating satisfies $D(M) = \det M \cdot D(I)$. Hint: expand each row in the standard basis, and show that only the terms with distinct basis vectors survive.
7. (B) Prove the expansion along a general row $i$: $\det A = \sum_j (-1)^{i+j} A_{ij} \det A^{(i,j)}$. Hint: move the row $i$ to the top by $i$ adjacent swaps.
8. (C) Let $A$ be an $n \times n$ matrix of integers, all of whose entries are $\pm 1$. Show that $\det A$ is divisible by $2^{n-1}$. Hint: subtract the first row from the others.

### Notes and history

Determinants appeared before matrices. Seki Takakazu in Japan in 1683 and Leibniz in 1693 used them to solve systems of linear equations. Cramer published his rule in 1750, and Vandermonde and Laplace developed the theory in the 1770s; the expansion of Laplace is from 1772. Cauchy used the word determinant in its present sense in 1812 and proved the multiplicativity. Weierstrass and Kronecker gave the characterization by the multilinear and alternating properties in lectures in the 1860s and 1870s, and this characterization is the base of the modern treatment.

The definition through `detRowAlternating` places the determinant inside the theory of alternating maps, and the formula of Leibniz is a theorem. This order keeps the general theory and the matrix computation in one place.

### Reference

<?reference?>
