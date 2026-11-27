---
title: The matrix of a linear map and the change of basis
kind: theory
modules:
  - Mathlib.LinearAlgebra.Matrix.ToLin
  - Mathlib.LinearAlgebra.Matrix.Basis
explains:
  E3: [LinearMap.toMatrix, Matrix.toLin]
  E2: [LinearMap.toMatrix_comp, LinearMap.toMatrix', Matrix.toLin', Matrix.mulVecLin, LinearMap.toMatrix_mulVec_repr, Module.Basis.toMatrix, Module.Basis.toMatrix_mul_toMatrix, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
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

## The matrix of a linear map and the change of basis

### Overview

A linear map is fixed by its values on a basis, and each value is fixed by its coordinates in a basis of the target. So a choice of bases turns a linear map into a table of numbers, its matrix. The column $j$ of the matrix holds the coordinates of the image of the basis vector $j$. The definition of the matrix product in Section 1 was made for one reason: the matrix of a composition is the product of the matrices.

This section proves that the passage from maps to matrices is a linear equivalence that turns composition into product, and it gives the formula for a change of basis. Two matrices of the same endomorphism in two bases are similar: $A' = P^{-1} A P$. The quantities that do not change under similarity, such as the trace, the determinant of Chapter 4 and the characteristic polynomial of Chapter 5, are therefore properties of the map and not of the bases.

### Definitions

In this section $R$ is a commutative ring. Let $M$ have the basis $b = (b_1, \dots, b_n)$ and $N$ the basis $c = (c_1, \dots, c_m)$.

**Definition (Matrix of a linear map).** The matrix of $f : M \to N$ in the bases $b$ and $c$ is the $m \times n$ matrix $[f]_{c,b}$ with
$$f(b_j) = \sum_{i=1}^m ([f]_{c,b})_{ij} \, c_i \qquad (1 \le j \le n).$$
So the entry $(i, j)$ is the coordinate $i$ of $f(b_j)$ in the basis $c$. When $M = N$ and $b = c$, write $[f]_b$.

::: mathlib
`LinearMap.toMatrix` · `Mathlib.LinearAlgebra.Matrix.ToLin`

The map `LinearMap.toMatrix b c : (M₁ →ₗ[R] M₂) ≃ₗ[R] Matrix m n R`, for a basis `b` of the source indexed by `n` and a basis `c` of the target indexed by `m`. It is a linear equivalence, so it contains the theorem that maps and matrices correspond. Note the order: the basis of the source comes first, but the rows of the matrix are indexed by the basis of the target. The ring is commutative, since the matrices of maps over a noncommutative ring compose in the opposite order.

<?decl LinearMap.toMatrix?>
:::

**Definition (Linear map of a matrix).** For an $m \times n$ matrix $A$, the map $T_A : M \to N$ is the linear map with $T_A(b_j) = \sum_i A_{ij} c_i$. On $R^n$ and $R^m$ with the standard bases, $T_A(x) = A x$.

::: mathlib
`Matrix.toLin` · `Mathlib.LinearAlgebra.Matrix.ToLin`

The inverse equivalence `Matrix.toLin b c : Matrix m n R ≃ₗ[R] (M₁ →ₗ[R] M₂)`. The lemmas `Matrix.toLin_toMatrix` and `LinearMap.toMatrix_toLin` say that the two maps are inverse.

<?decl Matrix.toLin?>
:::

::: mathlib
`Matrix.mulVecLin` · `Mathlib.LinearAlgebra.Matrix.ToLin`

The linear map `A.mulVecLin : (n → R) →ₗ[R] (m → R)`, `v ↦ A *ᵥ v`. It does not need a basis.

<?decl Matrix.mulVecLin?>
:::

::: mathlib
`Matrix.toLin'` · `Mathlib.LinearAlgebra.Matrix.ToLin`

The equivalence `Matrix.toLin' : Matrix m n R ≃ₗ[R] ((n → R) →ₗ[R] (m → R))` for the standard bases. Its value is `mulVecLin`. The prime marks the standard case, and the same convention holds for `LinearMap.toMatrix'`.

<?decl Matrix.toLin'?>
:::

::: mathlib
`LinearMap.toMatrix'` · `Mathlib.LinearAlgebra.Matrix.ToLin`

The matrix of a map `(n → R) →ₗ[R] (m → R)` in the standard bases. Its entry `(i, j)` is `f (Pi.single j 1) i`, the coordinate `i` of the image of the standard vector `j`.

<?decl LinearMap.toMatrix'?>
:::

**Definition (Change of basis matrix).** Let $b$ and $b'$ be two bases of $M$, with $n$ vectors each. The change of basis matrix $P_{b, b'}$ is the $n \times n$ matrix whose column $j$ holds the coordinates of $b'_j$ in the basis $b$:
$$b'_j = \sum_i (P_{b,b'})_{ij} \, b_i.$$
It is the matrix $[\mathrm{id}]_{b, b'}$ of the identity map, from the basis $b'$ to the basis $b$.

::: mathlib
`Module.Basis.toMatrix` · `Mathlib.LinearAlgebra.Matrix.Basis`

The matrix `b.toMatrix v` for a basis `b` and any family `v : ι' → M`, with `b.toMatrix v i j = b.repr (v j) i`. When `v` is a second basis `b'`, it is the change of basis matrix $P_{b,b'}$. The family need not be a basis: `b.toMatrix v` is the matrix of the coordinates of the vectors `v j`.

<?decl Module.Basis.toMatrix?>
:::

### Theorems and proofs

**Theorem (Coordinates of the image).** For $x \in M$, write $[x]_b \in R^n$ for its coordinate vector. Then
$$[f(x)]_c = [f]_{c,b} \, [x]_b.$$

*Proof.* Let $x = \sum_j x_j b_j$. Then
$$f(x) = \sum_j x_j f(b_j) = \sum_j x_j \sum_i A_{ij} c_i = \sum_i \Big( \sum_j A_{ij} x_j \Big) c_i,$$
with $A = [f]_{c,b}$. The coordinate $i$ of $f(x)$ is $\sum_j A_{ij} x_j$, which is the entry $i$ of the product $A [x]_b$. $\square$

::: mathlib
`LinearMap.toMatrix_mulVec_repr` · `Mathlib.LinearAlgebra.Matrix.ToLin`

The statement `toMatrix b c f *ᵥ b.repr x = c.repr (f x)`. The coordinates `b.repr x` are a finitely supported function; with a finite index, it coerces to a vector.

<?decl LinearMap.toMatrix_mulVec_repr?>
:::

**Theorem (Maps and matrices).** The map $f \mapsto [f]_{c,b}$ is a linear equivalence from $\operatorname{Hom}_R(M, N)$ to the $m \times n$ matrices over $R$. Its inverse is $A \mapsto T_A$. In particular $\operatorname{Hom}_R(M, N)$ is free of rank $m n$.

*Proof.* The map is linear: the coordinates of $(f + g)(b_j) = f(b_j) + g(b_j)$ are the sums of the coordinates, and the same holds for $r f$. It is injective: if $[f]_{c,b} = 0$, then $f(b_j) = 0$ for each $j$, so $f = 0$ by the universal property of a basis. It is surjective: for a matrix $A$, the map $T_A$ has $T_A(b_j) = \sum_i A_{ij} c_i$, so $[T_A]_{c,b} = A$. The matrices form a free module with the basis of the matrix units $E_{ij}$, and there are $m n$ of them. $\square$

**Theorem (Composition is product).** Let $P$ have a basis $d = (d_1, \dots, d_p)$, and let $g : M \to N$ and $f : N \to P$ be linear. Then
$$[f \circ g]_{d,b} = [f]_{d,c} \, [g]_{c,b}.$$
Also $[\mathrm{id}_M]_{b,b} = I$.

*Proof.* Let $A = [f]_{d,c}$ and $B = [g]_{c,b}$. For each $j$,
$$(f \circ g)(b_j) = f\Big( \sum_k B_{kj} c_k \Big) = \sum_k B_{kj} f(c_k) = \sum_k B_{kj} \sum_i A_{ik} d_i = \sum_i \Big( \sum_k A_{ik} B_{kj} \Big) d_i.$$
The coefficient of $d_i$ is $(A B)_{ij}$, so the column $j$ of $[f \circ g]_{d,b}$ is the column $j$ of $A B$. The scalars $B_{kj}$ and $A_{ik}$ were moved past each other in the step $B_{kj} A_{ik} = A_{ik} B_{kj}$, which uses that $R$ is commutative. For the identity, $\mathrm{id}(b_j) = b_j = \sum_i \delta_{ij} b_i$. $\square$

This theorem gives a second proof of the associativity of the matrix product, at least for the matrices over a commutative ring: composition of maps is associative, and the correspondence turns it into the product.

::: mathlib
`LinearMap.toMatrix_comp` · `Mathlib.LinearAlgebra.Matrix.ToLin`

The statement `toMatrix b d (f.comp g) = toMatrix c d f * toMatrix b c g`. The middle basis `c` must be the same on both sides.

<?decl LinearMap.toMatrix_comp?>
:::

For an endomorphism $f$ of $M$ with the basis $b$, the theorem says that $f \mapsto [f]_b$ is a ring isomorphism from $\operatorname{End}_R(M)$ to the $n \times n$ matrices. Mathlib records this as the algebra equivalence `LinearMap.toMatrixAlgEquiv`.

**Theorem (Change of basis matrices).** Let $b, b', b''$ be bases of $M$. Then $P_{b,b'} P_{b',b''} = P_{b,b''}$ and $P_{b,b} = I$. So $P_{b,b'}$ is invertible, with inverse $P_{b',b}$. For each $x$, $[x]_b = P_{b,b'} [x]_{b'}$.

*Proof.* $P_{b,b'} = [\mathrm{id}]_{b,b'}$. The composition theorem gives $[\mathrm{id}]_{b,b'} [\mathrm{id}]_{b',b''} = [\mathrm{id} \circ \mathrm{id}]_{b,b''} = [\mathrm{id}]_{b,b''}$. With $b'' = b$, this reads $P_{b,b'} P_{b',b} = P_{b,b} = I$, and the same with the roles swapped. The last claim is the theorem on coordinates for the identity map. $\square$

::: mathlib
`Module.Basis.toMatrix_mul_toMatrix` · `Mathlib.LinearAlgebra.Matrix.Basis`

The rule `b.toMatrix b' * b'.toMatrix b'' = b.toMatrix b''`. The last argument `b''` is any family; only `b'` must be a basis. The inverse pair is `Module.Basis.toMatrix_mul_toMatrix_flip`.

<?decl Module.Basis.toMatrix_mul_toMatrix?>
:::

**Theorem (Change of basis).** Let $b, b'$ be bases of $M$ and $c, c'$ bases of $N$, and let $f : M \to N$ be linear. Then
$$[f]_{c,b} = P_{c,c'} \, [f]_{c',b'} \, P_{b',b}.$$
For an endomorphism with $c = b$ and $c' = b'$, put $P = P_{b,b'}$. Then $[f]_{b'} = P^{-1} [f]_b P$.

*Proof.* Write $f = \mathrm{id}_N \circ f \circ \mathrm{id}_M$. Read it with the bases $b \to b' \to c' \to c$: the right $\mathrm{id}_M$ goes from $b$ to $b'$, the map $f$ from $b'$ to $c'$, and the left $\mathrm{id}_N$ from $c'$ to $c$. The composition theorem, applied twice, gives
$$[f]_{c,b} = [\mathrm{id}]_{c,c'} [f]_{c',b'} [\mathrm{id}]_{b',b}.$$
For the second statement, take $c = b$ and $c' = b'$, and swap the roles of $b$ and $b'$: $[f]_{b'} = P_{b',b} [f]_b P_{b,b'} = P^{-1} [f]_b P$. $\square$

::: mathlib
`basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix` · `Mathlib.LinearAlgebra.Matrix.Basis`

The formula `c.toMatrix c' * toMatrix b' c' f * b'.toMatrix b = toMatrix b c f`. It is the theorem above with the Mathlib names: `c.toMatrix c'` is $P_{c,c'}$ and `b'.toMatrix b` is $P_{b',b}$. The two halves are `basis_toMatrix_mul_linearMap_toMatrix` and `linearMap_toMatrix_mul_basis_toMatrix`.

<?decl basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix?>
:::

**Definition (Similar matrices).** Two $n \times n$ matrices $A$ and $A'$ are similar if $A' = P^{-1} A P$ for an invertible $P$. By the theorem, the matrices of one endomorphism in all the bases form one class of similar matrices.

**Corollary (Trace of an endomorphism).** For $f \in \operatorname{End}_R(M)$, the trace $\operatorname{tr} [f]_b$ does not depend on the basis $b$.

*Proof.* Two matrices of $f$ are similar, and $\operatorname{tr}(P^{-1} A P) = \operatorname{tr} A$ by the cyclic law of Section 1. $\square$

### Examples

**Example (A rotation).** Let $\rho : \mathbb{R}^2 \to \mathbb{R}^2$ be the rotation by $\theta$. Then $\rho(e_1) = (\cos\theta, \sin\theta)$ and $\rho(e_2) = (-\sin\theta, \cos\theta)$. These are the columns of the matrix:
$$[\rho] = \begin{pmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta \end{pmatrix}.$$
The composition of the rotations by $\alpha$ and $\beta$ is the rotation by $\alpha + \beta$. The product of the two matrices has the entry $(1,1)$ equal to $\cos\alpha \cos\beta - \sin\alpha \sin\beta$, and the composition theorem says that it is $\cos(\alpha + \beta)$. This is the addition formula of the cosine, read from matrices.

**Example (The derivative on $P_3$).** In the basis $1, x, x^2, x^3$ of $P_3$, the derivative sends $1 \mapsto 0$, $x \mapsto 1$, $x^2 \mapsto 2x$ and $x^3 \mapsto 3x^2$. So
$$[D] = \begin{pmatrix} 0 & 1 & 0 & 0 \\ 0 & 0 & 2 & 0 \\ 0 & 0 & 0 & 3 \\ 0 & 0 & 0 & 0 \end{pmatrix}.$$
For $p = 5 - x + 4x^3$, the coordinates are $(5, -1, 0, 4)$, and $[D](5, -1, 0, 4) = (-1, 0, 12, 0)$, the coordinates of $p' = -1 + 12 x^2$. The matrix is strictly upper triangular, so its fourth power is $0$, as $D^4 = 0$ on $P_3$.

**Example (A change of basis that diagonalizes).** Let $f : \mathbb{Q}^2 \to \mathbb{Q}^2$ have the matrix $A = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ in the standard basis $e$. Take the new basis $b'_1 = (1, 1)$ and $b'_2 = (1, -1)$. Then $f(b'_1) = (3, 3) = 3 b'_1$ and $f(b'_2) = (1, -1) = b'_2$. So $[f]_{b'} = \begin{pmatrix} 3 & 0 \\ 0 & 1 \end{pmatrix}$. The change of basis matrix is $P = P_{e,b'} = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$, with the vectors $b'_j$ as columns, and $P^{-1} = \frac{1}{2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$. Check the formula:
$$A P = \begin{pmatrix} 3 & 1 \\ 3 & -1 \end{pmatrix}, \qquad P^{-1} A P = \frac{1}{2} \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix} \begin{pmatrix} 3 & 1 \\ 3 & -1 \end{pmatrix} = \frac{1}{2} \begin{pmatrix} 6 & 0 \\ 0 & 2 \end{pmatrix} = \begin{pmatrix} 3 & 0 \\ 0 & 1 \end{pmatrix}.$$
The traces agree: $2 + 2 = 3 + 1$.

**Example (A map between different spaces).** Let $f : P_2 \to \mathbb{R}^2$, $f(p) = (p(0), p(1))$, with the basis $1, x, x^2$ of $P_2$ and the standard basis of $\mathbb{R}^2$. Then $f(1) = (1, 1)$, $f(x) = (0, 1)$ and $f(x^2) = (0, 1)$. So
$$[f] = \begin{pmatrix} 1 & 0 & 0 \\ 1 & 1 & 1 \end{pmatrix}.$$
In the basis $1, x, x^2 - x$ the last column becomes $f(x^2 - x) = (0, 0)$, which shows a vector of the kernel.

**Counterexample (Similar or not).** The matrices $I$ and $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ have the same trace $2$, but they are not similar: $P^{-1} I P = I$ for each invertible $P$, so the class of $I$ contains only $I$. Equal traces do not imply similarity.

### The library around it

The correspondence between maps and matrices is in `Mathlib.LinearAlgebra.Matrix.ToLin`, and the change of basis is in `Mathlib.LinearAlgebra.Matrix.Basis`. The ring isomorphism for endomorphisms is `LinearMap.toMatrixAlgEquiv`, with the standard version `LinearMap.toMatrixAlgEquiv'`. The matrix of a linear map can also be read from the coordinates of each column: `LinearMap.toMatrix_apply` and `Module.Basis.toMatrix_apply` reduce the entries to `repr`.

In a proof about a concrete map on `Fin n → R`, the standard versions with a prime avoid the bases. In a proof about an abstract space, choose a basis with `Module.finBasis K V`, which exists for a finite dimensional space, and work with `toMatrix`.

### Exercises

1. (A) Write the matrix of the reflection $(x, y) \mapsto (y, x)$ of $\mathbb{R}^2$ in the standard basis and in the basis $(1, 1), (1, -1)$.
2. (A) Write the matrix of $p \mapsto x p$ from $P_2$ to $P_3$ in the monomial bases.
3. (A) Let $f(x, y, z) = (x + y, y + z)$. Write $[f]$ in the standard bases and compute $f(1, 2, 3)$ with it.
4. (B) Let $P_{b,b'} = \begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix}$ with $b$ the standard basis of $\mathbb{R}^2$. Find $b'$, and find the coordinates of $(3, 5)$ in $b'$.
5. (B) Let $f \in \operatorname{End}(V)$ and $U$ a subspace with $f(U) \subseteq U$. Show that in a basis of $V$ that extends a basis of $U$, the matrix of $f$ has the block form $\begin{pmatrix} A & B \\ 0 & C \end{pmatrix}$.
6. (B) Show that the matrices $\begin{pmatrix} 1 & 1 \\ 0 & 2 \end{pmatrix}$ and $\begin{pmatrix} 1 & 0 \\ 0 & 2 \end{pmatrix}$ are similar over $\mathbb{Q}$. Hint: find a basis of eigenvectors of the first one.
7. (B) Let $f$ have the matrix $A$ in a basis $b$. Find the matrix of $f$ in the basis $b$ read in the reverse order $b_n, \dots, b_1$.
8. (C) Show that each $n \times n$ matrix $A$ over a field with $\operatorname{tr} A = 0$ is similar to a matrix with only $0$ on the diagonal. Hint: if $A$ is not a scalar matrix, find $v$ with $v$ and $A v$ independent, and use a basis that starts with $v, A v$; then argue by induction.

### Notes and history

The representation of linear substitutions by arrays of coefficients is in Cayley's memoir of 1858. The study of similar matrices, and of the invariants of a matrix under similarity, begins with Weierstrass in 1868 and Jordan in 1870, and Frobenius gave it its modern form around 1878. The abstract point of view, with a linear map and its matrices in all bases, became standard with the books of van der Waerden and of Halmos.

The decision to state the correspondence as a linear equivalence `toMatrix b c` makes the inverse `toLin b c` and the round trip lemmas automatic, and it lets a proof move a statement about maps to a statement about matrices with one rewrite.

### Reference

<?reference?>
