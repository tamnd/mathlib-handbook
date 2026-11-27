---
title: Matrices and their algebra
kind: theory
modules:
  - Mathlib.LinearAlgebra.Matrix.Defs
  - Mathlib.Data.Matrix.Mul
  - Mathlib.Data.Matrix.Diagonal
  - Mathlib.LinearAlgebra.Matrix.Trace
explains:
  E3: [Matrix, Matrix.mulVec]
  E2: [Matrix.of, Matrix.mul_apply, Matrix.transpose, Matrix.diagonal, Matrix.mul_assoc, Matrix.trace, Matrix.trace_mul_comm]
  E1: auto
families: []
requires: [V07.C02, V03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Matrices and their algebra

### Overview

A system of linear equations is fixed by its table of coefficients. The system $2x + 3y = 5$, $x - y = 0$ is the table $\begin{pmatrix} 2 & 3 \\ 1 & -1 \end{pmatrix}$ with the right side $(5, 0)$. A matrix is such a table. Matrices of the right sizes add and multiply, and the product is built so that it matches the composition of the linear maps that the matrices describe. The result is an algebra: the square matrices of size $n$ form a ring, which is not commutative for $n \ge 2$.

This section defines matrices with entries in a ring, the operations on them, and proves the laws: the associativity of the product, the unit, the rules for the transpose, and the cyclic law of the trace. Each proof is a computation with finite sums. Section 2 explains the product through linear maps, and then associativity becomes the associativity of composition.

### Definitions

**Definition (Matrix).** Let $m$ and $n$ be finite sets of indices and $R$ a ring. An $m \times n$ matrix over $R$ is a family $A = (A_{ij})_{i \in m, j \in n}$ of elements of $R$. The index $i$ is the row and $j$ is the column. When $m = \{1, \dots, p\}$ and $n = \{1, \dots, q\}$, $A$ is a $p \times q$ matrix, a table with $p$ rows and $q$ columns. The matrices of a fixed size add entrywise and are multiplied by scalars entrywise.

::: mathlib
`Matrix` · `Mathlib.LinearAlgebra.Matrix.Defs`

The type `Matrix m n α` is defined as `m → n → α`: a matrix is a function of the row and the column. The index types are arbitrary types, not only `Fin p`, so a matrix can be indexed by the elements of a group or by a sum type `m ⊕ m'` for block matrices. The entry is `A i j`. The type is a new definition and not an abbreviation, so that the product `*` on matrices does not clash with the pointwise product on functions.

<?decl Matrix?>
:::

::: mathlib
`Matrix.of` · `Mathlib.LinearAlgebra.Matrix.Defs`

The equivalence `Matrix.of : (m → n → α) ≃ Matrix m n α` turns a function into a matrix. It is the identity on the data, but it changes the type, so the product of matrices applies to the result. The notation `!![1, 2; 3, 4]` is `Matrix.of ![![1, 2], ![3, 4]]`, the $2 \times 2$ matrix with rows $(1, 2)$ and $(3, 4)$.

<?decl Matrix.of?>
:::

**Definition (Product).** Let $A$ be an $l \times m$ matrix and $B$ an $m \times n$ matrix. Their product is the $l \times n$ matrix
$$(A B)_{ik} = \sum_{j \in m} A_{ij} B_{jk}.$$
The entry $(i, k)$ of $A B$ is the product of the row $i$ of $A$ and the column $k$ of $B$. The product of $A$ with a column vector $v \in R^m$ is the vector $(A v)_i = \sum_j A_{ij} v_j$.

::: mathlib
`Matrix.mul_apply` · `Mathlib.Data.Matrix.Mul`

The formula `(M * N) i k = ∑ j, M i j * N j k`. The product `*` needs the middle index type to be a `Fintype`, so that the sum is finite.

<?decl Matrix.mul_apply?>
:::

::: mathlib
`Matrix.mulVec` · `Mathlib.Data.Matrix.Mul`

The product of a matrix and a column vector, `M.mulVec v`, with the notation `M *ᵥ v` (open the scope `Matrix`). The value is `(M *ᵥ v) i = ∑ j, M i j * v j`, the dot product of the row `i` with `v`. The product of a row vector and a matrix is `Matrix.vecMul`, with the notation `v ᵥ* M`. Mathlib keeps vectors as functions `n → α`, and it has no separate type of column matrices.

<?decl Matrix.mulVec?>
:::

**Definition (Identity and diagonal matrices).** For a family $d = (d_i)_{i \in n}$, the diagonal matrix $\operatorname{diag}(d)$ has the entries $d_i$ on the diagonal and $0$ elsewhere. The identity matrix is $I = \operatorname{diag}(1, \dots, 1)$, with entries $I_{ij} = \delta_{ij}$, where $\delta_{ij} = 1$ if $i = j$ and $0$ otherwise.

::: mathlib
`Matrix.diagonal` · `Mathlib.Data.Matrix.Diagonal`

The matrix `diagonal d` with `diagonal d i j = if i = j then d i else 0`. It needs `DecidableEq n` to decide `i = j`. The identity matrix `1` is `diagonal (fun _ => 1)`.

<?decl Matrix.diagonal?>
:::

**Definition (Transpose).** The transpose of an $m \times n$ matrix $A$ is the $n \times m$ matrix $A^{\mathsf{T}}$ with $(A^{\mathsf{T}})_{ji} = A_{ij}$. Its rows are the columns of $A$.

::: mathlib
`Matrix.transpose` · `Mathlib.LinearAlgebra.Matrix.Defs`

The transpose `Aᵀ`, with `Aᵀ i j = A j i`. The superscript `ᵀ` is typed `\^T`. The transpose is in the scope `Matrix`.

<?decl Matrix.transpose?>
:::

**Definition (Trace).** The trace of a square matrix $A$ is the sum of its diagonal entries, $\operatorname{tr} A = \sum_i A_{ii}$.

::: mathlib
`Matrix.trace` · `Mathlib.LinearAlgebra.Matrix.Trace`

The trace `A.trace = ∑ i, A i i`. It is additive and linear in `A`; the bundled linear map is `Matrix.traceLinearMap`.

<?decl Matrix.trace?>
:::

### Theorems and proofs

**Theorem (Associativity).** Let $A$ be $k \times l$, $B$ be $l \times m$ and $C$ be $m \times n$. Then $(A B) C = A (B C)$.

*Proof.* Compare the entries $(i, s)$. On the left,
$$((A B) C)_{is} = \sum_{r \in m} (A B)_{ir} C_{rs} = \sum_{r \in m} \Big( \sum_{j \in l} A_{ij} B_{jr} \Big) C_{rs} = \sum_{r \in m} \sum_{j \in l} A_{ij} B_{jr} C_{rs}.$$
The last step uses the distributive law and the associativity of the product in $R$. On the right, in the same way,
$$(A (B C))_{is} = \sum_{j \in l} A_{ij} \Big( \sum_{r \in m} B_{jr} C_{rs} \Big) = \sum_{j \in l} \sum_{r \in m} A_{ij} B_{jr} C_{rs}.$$
The two double sums are sums of the same finite family over $l \times m$, in two orders. A finite sum does not depend on the order, by Volume 3. $\square$

::: mathlib
`Matrix.mul_assoc` · `Mathlib.Data.Matrix.Mul`

The law `L * M * N = L * (M * N)` for matrices over a nonunital semiring. The proof in Mathlib is the proof above: it expands the entries and swaps the two sums with `Finset.sum_comm`. For square matrices, the general lemma `mul_assoc` of a ring also applies.

<?decl Matrix.mul_assoc?>
:::

**Theorem (Ring of matrices).** The $n \times n$ matrices over $R$ form a ring, with the entrywise sum and the product above. The unit is $I$. The product distributes over the sum.

*Proof.* Associativity is the last theorem. For the unit, $(A I)_{ik} = \sum_j A_{ij} \delta_{jk} = A_{ik}$, since only the term $j = k$ is nonzero, and in the same way $(I A)_{ik} = A_{ik}$. For the distributive law, $(A (B + C))_{ik} = \sum_j A_{ij}(B_{jk} + C_{jk}) = \sum_j A_{ij} B_{jk} + \sum_j A_{ij} C_{jk}$, and the same on the other side. The sum is entrywise, so it is an abelian group. $\square$

**Theorem (Transpose of a product).** Let $R$ be commutative, $A$ be $l \times m$ and $B$ be $m \times n$. Then $(A B)^{\mathsf{T}} = B^{\mathsf{T}} A^{\mathsf{T}}$. Also $(A^{\mathsf{T}})^{\mathsf{T}} = A$ and $(A + B')^{\mathsf{T}} = A^{\mathsf{T}} + B'^{\mathsf{T}}$ for $B'$ of the size of $A$.

*Proof.* The entry $(k, i)$ of the left side is $(A B)_{ik} = \sum_j A_{ij} B_{jk}$. The entry $(k, i)$ of the right side is $\sum_j (B^{\mathsf{T}})_{kj} (A^{\mathsf{T}})_{ji} = \sum_j B_{jk} A_{ij}$. The two sums agree term by term because $R$ is commutative. The other two rules are clear from the definition, entry by entry. $\square$

Over a noncommutative ring, such as the quaternions, the first rule fails already for $1 \times 1$ matrices: $(a b)^{\mathsf{T}} = a b$ and $b^{\mathsf{T}} a^{\mathsf{T}} = b a$.

**Theorem (Cyclic law of the trace).** Let $R$ be commutative, $A$ be $m \times n$ and $B$ be $n \times m$. Then $\operatorname{tr}(A B) = \operatorname{tr}(B A)$. Consequently, for square $A$ and invertible $P$ of the same size, $\operatorname{tr}(P^{-1} A P) = \operatorname{tr} A$.

*Proof.* By definition,
$$\operatorname{tr}(A B) = \sum_{i \in m} \sum_{j \in n} A_{ij} B_{ji}, \qquad \operatorname{tr}(B A) = \sum_{j \in n} \sum_{i \in m} B_{ji} A_{ij}.$$
The two double sums run over the same finite set $m \times n$, and the terms agree because $R$ is commutative. For the second claim, apply the first with the matrices $P^{-1} A$ and $P$: $\operatorname{tr}((P^{-1} A) P) = \operatorname{tr}(P (P^{-1} A)) = \operatorname{tr} A$. $\square$

The matrices $A$ and $B$ need not be square. For a $1 \times n$ row $u$ and an $n \times 1$ column $v$, the law reads $\operatorname{tr}(u v) = u v = \sum u_j v_j = \operatorname{tr}(v u)$, the dot product as the trace of an $n \times n$ matrix.

::: mathlib
`Matrix.trace_mul_comm` · `Mathlib.LinearAlgebra.Matrix.Trace`

The law `trace (A * B) = trace (B * A)` for `A : Matrix m n R` and `B : Matrix n m R`. The cyclic form for three factors is `Matrix.trace_mul_cycle`.

<?decl Matrix.trace_mul_comm?>
:::

**Theorem (Linear systems as products).** The system of $p$ equations $\sum_{j=1}^q a_{ij} x_j = b_i$, $1 \le i \le p$, is the equation $A x = b$, with $A = (a_{ij})$, $x \in R^q$ and $b \in R^p$. If $A x_0 = b$, then the set of solutions is $x_0 + \ker A$, where $\ker A = \{x : A x = 0\}$.

*Proof.* The entry $i$ of $A x$ is $\sum_j a_{ij} x_j$, so the two forms agree. The map $x \mapsto A x$ is linear by the distributive law. If $A x_0 = b$, then $A x = b$ holds if and only if $A(x - x_0) = 0$, that is, $x - x_0 \in \ker A$. $\square$

### Examples

**Example (A product of $2 \times 2$ matrices).** Let
$$A = \begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}, \qquad B = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}.$$
Then
$$A B = \begin{pmatrix} 1 \cdot 0 + 2 \cdot 1 & 1 \cdot 1 + 2 \cdot 0 \\ 3 \cdot 0 + 4 \cdot 1 & 3 \cdot 1 + 4 \cdot 0 \end{pmatrix} = \begin{pmatrix} 2 & 1 \\ 4 & 3 \end{pmatrix}, \qquad B A = \begin{pmatrix} 3 & 4 \\ 1 & 2 \end{pmatrix}.$$
Multiplication by $B$ on the right swaps the columns of $A$, and on the left it swaps the rows. So $A B \neq B A$. The traces agree: $\operatorname{tr}(A B) = 2 + 3 = 5 = 3 + 2 = \operatorname{tr}(B A)$.

**Example (Nilpotent matrices and zero divisors).** Let $N = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. Then $N^2 = \begin{pmatrix} 0 \cdot 0 + 1 \cdot 0 & 0 \cdot 1 + 1 \cdot 0 \\ 0 & 0 \end{pmatrix} = 0$. So the ring of $2 \times 2$ matrices has nonzero elements whose square is $0$. The $3 \times 3$ matrix with $1$ on the entries $(1, 2)$ and $(2, 3)$ and $0$ elsewhere has a nonzero square, the matrix with a single $1$ at $(1, 3)$, and its cube is $0$.

**Example (Matrix units).** Let $E_{ij}$ be the $n \times n$ matrix with $1$ at $(i, j)$ and $0$ elsewhere. The product rule gives $E_{ij} E_{kl} = \delta_{jk} E_{il}$: the only nonzero term of $(E_{ij} E_{kl})_{ab} = \sum_c (E_{ij})_{ac} (E_{kl})_{cb}$ needs $a = i$, $c = j = k$ and $b = l$. The $n^2$ matrices $E_{ij}$ form a basis of the module of $n \times n$ matrices, and each matrix is $A = \sum_{i,j} A_{ij} E_{ij}$. In Mathlib, $E_{ij}$ is `Matrix.single i j 1`.

**Example (No matrices with $AB - BA = I$).** Over $\mathbb{Q}$, there are no $n \times n$ matrices $A, B$ with $A B - B A = I$, for $n \ge 1$. The trace of the left side is $\operatorname{tr}(A B) - \operatorname{tr}(B A) = 0$, by the cyclic law. The trace of the right side is $n \neq 0$. Over $\mathbb{F}_p$ the argument fails for $n = p$, since $p = 0$ in $\mathbb{F}_p$. Exercise 8 builds such matrices of size $p$.

**Example (A linear system).** The system $x + 2y + z = 4$, $2x + y - z = 1$ is $A v = b$ with $A = \begin{pmatrix} 1 & 2 & 1 \\ 2 & 1 & -1 \end{pmatrix}$ and $b = (4, 1)$. Subtract twice the first equation from the second: $-3y - 3z = -7$, so $y = 7/3 - z$. Then $x = 4 - 2y - z = -2/3 + z$. With $z = 0$ this gives the solution $v_0 = (-2/3, 7/3, 0)$. Check: $-2/3 + 14/3 = 4$ and $-4/3 + 7/3 = 1$. The kernel is the line of the vectors $(t, -t, t)$: $t - 2t + t = 0$ and $2t - t - t = 0$. So the solution set is $v_0 + \mathbb{Q}(1, -1, 1)$.

### The library around it

The type `Matrix` and its basic operations are in `Mathlib.LinearAlgebra.Matrix.Defs`. The product and `mulVec` are in `Mathlib.Data.Matrix.Mul`, the diagonal matrices and the identity in `Mathlib.Data.Matrix.Diagonal`, and the trace in `Mathlib.LinearAlgebra.Matrix.Trace`. The ring structure on `Matrix n n R` is the instance `Matrix.semiring` and its relatives, and the algebra structure over a commutative `R` is `Matrix.instAlgebra`. Block matrices use `Matrix.fromBlocks`, with index type `m ⊕ n`.

For computation, the notation `!![a, b; c, d]` with numerals works with `simp` and `norm_num`. The tactic `decide` can check identities of small matrices over `ℤ` or `ZMod n`. The lemma `Matrix.ext` reduces an equality of matrices to all the entries, and the tactic `ext i j` applies it.

### Exercises

1. (A) Compute $A^2$, $A^3$ and $A^n$ for $A = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$. Hint: write $A = I + N$ with $N^2 = 0$.
2. (A) Find all $2 \times 2$ matrices that commute with $\begin{pmatrix} 1 & 0 \\ 0 & 2 \end{pmatrix}$.
3. (A) Show that $(A B)^{\mathsf{T}} = B^{\mathsf{T}} A^{\mathsf{T}}$ for $A = \begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix}$ and $B = \begin{pmatrix} 3 & 0 \\ 1 & 1 \end{pmatrix}$ by computing both sides.
4. (B) Show that a matrix that commutes with all $n \times n$ matrices is a scalar multiple of $I$. Hint: compare $E_{ij} A$ and $A E_{ij}$.
5. (B) Show that $\operatorname{tr}(A B C) = \operatorname{tr}(C A B)$, and find $2 \times 2$ matrices with $\operatorname{tr}(A B C) \neq \operatorname{tr}(B A C)$.
6. (B) Let $A$ be an $n \times n$ real matrix with $A^{\mathsf{T}} A = 0$. Show that $A = 0$. Hint: compute the trace of $A^{\mathsf{T}} A$.
7. (B) Show that the upper triangular matrices form a subring of the ring of $n \times n$ matrices. Hint: $A_{ij} = 0$ for $i > j$; look at the terms of $(A B)_{ik}$ for $i > k$.
8. (C) Over $\mathbb{F}_p$, let $V$ be the space of the polynomials of degree less than $p$, with the basis $1, x, \dots, x^{p-1}$. Let $D$ be the derivative, and let $X$ send $x^k$ to $x^{k+1}$ for $k < p - 1$ and $x^{p-1}$ to $0$. Show that $D X - X D = I$ on $V$, and write the two $p \times p$ matrices. Hint: check the basis vectors; for $x^{p-1}$ use $p - 1 = -1$ in $\mathbb{F}_p$.

### Notes and history

Arthur Cayley introduced the algebra of matrices in his "Memoir on the theory of matrices" of 1858. He defined the product so that it matches the composition of linear substitutions, and he noted that it is not commutative. The word "matrix" is due to James Joseph Sylvester in 1850, for the table from which determinants are cut. The trace and its invariance under conjugation appear in the work of Frobenius on group characters in the 1890s.

The choice of `Matrix m n α := m → n → α` with arbitrary index types makes block matrices and matrices indexed by a group natural. The cost is that each statement must say which index types are finite and which have decidable equality.

### Reference

<?reference?>
