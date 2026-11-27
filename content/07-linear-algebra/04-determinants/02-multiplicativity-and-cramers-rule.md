---
title: Multiplicativity, the adjugate and the rule of Cramer
kind: theory
modules:
  - Mathlib.LinearAlgebra.Determinant
  - Mathlib.LinearAlgebra.Matrix.Adjugate
  - Mathlib.LinearAlgebra.Matrix.NonsingularInverse
  - Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
  - Mathlib.LinearAlgebra.Vandermonde
explains:
  E3: [Matrix.det_mul, Matrix.isUnit_iff_isUnit_det, Matrix.adjugate, Matrix.mul_adjugate, Matrix.cramer, LinearMap.det]
  E2: [Matrix.det_mul_aux, Matrix.det_conj, Matrix.adjugate_apply, Matrix.mulVec_cramer, Matrix.cramer_eq_adjugate_mulVec, Matrix.inv_def, Matrix.nonsing_inv_mul, Matrix.exists_mulVec_eq_zero_iff, LinearMap.det_toMatrix, LinearMap.det_comp, Matrix.det_vandermonde]
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

## Multiplicativity, the adjugate and the rule of Cramer

### Overview

The determinant turns the product of matrices into the product of scalars: $\det(A B) = \det A \det B$. With the adjugate matrix, which satisfies $A \operatorname{adj} A = \det A \cdot I$, this theorem decides when a matrix is invertible: over a commutative ring $R$, the matrix $A$ is invertible exactly when $\det A$ is a unit of $R$. Over a field the condition is $\det A \neq 0$. Over $\mathbb{Z}$ it is $\det A = \pm 1$.

This section proves the multiplicativity and the adjugate identity, derives the criterion for invertibility and the rule of Cramer, and defines the determinant of an endomorphism of a free module. The examples invert explicit matrices and solve an explicit system.

### Definitions

**Definition (Adjugate).** For an $n \times n$ matrix $A$, the adjugate $\operatorname{adj} A$ is the $n \times n$ matrix with the entries
$$(\operatorname{adj} A)_{ij} = (-1)^{i+j} \det A^{(j,i)},$$
where $A^{(j,i)}$ is $A$ with the row $j$ and the column $i$ deleted. Note the swap of the indices.

**Definition (Cramer map).** For an $n \times n$ matrix $A$ and $b \in R^n$, the vector $\operatorname{cramer}(A, b)$ has the entries $\det A[\text{col } i := b]$, the determinant of $A$ with the column $i$ replaced by $b$.

::: mathlib
`Matrix.cramer` · `Mathlib.LinearAlgebra.Matrix.Adjugate`

The linear map `A.cramer : (n → R) →ₗ[R] (n → R)`. Mathlib defines it first, as the map `b ↦ (i ↦ (A.updateCol i b).det)`, and defines the adjugate from it.

<?decl Matrix.cramer?>
:::

::: mathlib
`Matrix.adjugate` · `Mathlib.LinearAlgebra.Matrix.Adjugate`

The adjugate `A.adjugate`. Its row `i` is `Aᵀ.cramer (Pi.single i 1)`. The expansion along a column shows that this definition agrees with the cofactor formula above.

<?decl Matrix.adjugate?>
:::

::: mathlib
`Matrix.adjugate_apply` · `Mathlib.LinearAlgebra.Matrix.Adjugate`

The entry formula `A.adjugate i j = (A.updateRow j (Pi.single i 1)).det`: replace the row `j` of `A` by the basis vector `e_i`. The expansion along the row `j` reduces this to the signed minor.

<?decl Matrix.adjugate_apply?>
:::

### Theorems and proofs

**Theorem (Multiplicativity).** For $n \times n$ matrices $M$ and $N$ over a commutative ring, $\det(M N) = \det M \det N$.

*Proof.* By the formula of Leibniz and the definition of the product,
$$\det(M N) = \sum_{\sigma} \operatorname{sgn} \sigma \prod_i \sum_k M_{\sigma(i), k} N_{k, i}.$$
Expand the product of sums: it is a sum over all functions $p : n \to n$, which choose one $k = p(i)$ for each $i$. So
$$\det(M N) = \sum_{p} \Bigl(\prod_i N_{p(i), i}\Bigr) \sum_\sigma \operatorname{sgn} \sigma \prod_i M_{\sigma(i), p(i)}.$$
The inner sum is the determinant of the matrix $M_p$ whose column $i$ is the column $p(i)$ of $M$. There are two cases.

If $p$ is not injective, then $p(i) = p(j)$ for some $i \neq j$, so $M_p$ has two equal columns and $\det M_p = 0$, by the alternating property and the transpose theorem of Section 1. Since $n$ is finite, the injective maps $p$ are the permutations $\tau$. For a permutation, $M_\tau$ is $M$ with the columns permuted by $\tau$, so $\det M_\tau = \operatorname{sgn} \tau \det M$. So
$$\det(M N) = \det M \sum_\tau \operatorname{sgn} \tau \prod_i N_{\tau(i), i} = \det M \det N. \qquad \square$$

::: mathlib
`Matrix.det_mul` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The statement `(M * N).det = M.det * N.det`. The proof in Mathlib follows the same plan: it expands the product into a sum over all functions `p : n → n` and splits the sum into the bijective and the other maps.

<?decl Matrix.det_mul?>
:::

::: mathlib
`Matrix.det_mul_aux` · `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`

The key step: for a map `p` that is not bijective, `∑ σ, sign σ * ∏ x, M (σ x) (p x) * N (p x) x = 0`. It is the case of the equal columns in the proof.

<?decl Matrix.det_mul_aux?>
:::

**Corollary (Consequences).** $\det I = 1$, $\det(M N) = \det(N M)$, and $\det(P M P^{-1}) = \det M$ for an invertible $P$.

*Proof.* $I$ is diagonal with the diagonal $1$. The second claim holds since $R$ is commutative. For the third, $\det(P M P^{-1}) = \det P \det M \det P^{-1} = \det M \det(P P^{-1}) = \det M$. $\square$

::: mathlib
`Matrix.det_conj` · `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`

For `IsUnit M`: `(M * N * M⁻¹).det = N.det`. Similar matrices have the same determinant.

<?decl Matrix.det_conj?>
:::

**Theorem (Adjugate identity).** $A \operatorname{adj} A = \operatorname{adj} A \cdot A = \det A \cdot I$.

*Proof.* The entry $(i, j)$ of $A \operatorname{adj} A$ is
$$\sum_k A_{ik} (-1)^{j+k} \det A^{(j,k)}.$$
Let $A'$ be $A$ with the row $j$ replaced by the row $i$. The minors $A'^{(j,k)}$ do not contain the row $j$, so $A'^{(j,k)} = A^{(j,k)}$. So the sum is the expansion of $\det A'$ along the row $j$. If $i = j$, then $A' = A$ and the entry is $\det A$. If $i \neq j$, then $A'$ has two equal rows, the rows $i$ and $j$, and the entry is $0$. So $A \operatorname{adj} A = \det A \cdot I$. The same argument with the expansion along a column gives $\operatorname{adj} A \cdot A = \det A \cdot I$. $\square$

::: mathlib
`Matrix.mul_adjugate` · `Mathlib.LinearAlgebra.Matrix.Adjugate`

The statement `A * A.adjugate = A.det • 1`. Chapter 5 applies it to the matrix `X • 1 - A` over the ring of polynomials, in the proof of the theorem of Cayley and Hamilton.

<?decl Matrix.mul_adjugate?>
:::

**Theorem (Invertibility).** Let $A$ be a square matrix over a commutative ring $R$. The following are equivalent: (a) $A$ has an inverse matrix; (b) $A$ has a left inverse; (c) $\det A$ is a unit of $R$. In this case $A^{-1} = (\det A)^{-1} \operatorname{adj} A$.

*Proof.* (a) implies (b) by definition. If $B A = I$, then $\det B \det A = \det I = 1$, so $\det A$ is a unit: (b) implies (c). If $\det A$ is a unit, let $B = (\det A)^{-1} \operatorname{adj} A$. By the adjugate identity, $A B = B A = I$: (c) implies (a). $\square$

So a left inverse of a square matrix is also a right inverse. For linear maps of an infinite dimensional space this fails, as the shift of Chapter 2 shows.

::: mathlib
`Matrix.isUnit_iff_isUnit_det` · `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`

The statement `IsUnit A ↔ IsUnit A.det`. Over a field, `isUnit_iff_ne_zero` turns the right side into `A.det ≠ 0`.

<?decl Matrix.isUnit_iff_isUnit_det?>
:::

::: mathlib
`Matrix.inv_def` · `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`

Mathlib defines `A⁻¹` for each square matrix: `A⁻¹ = Ring.inverse A.det • A.adjugate`. Here `Ring.inverse x` is the inverse of `x` if `x` is a unit and `0` otherwise. So a singular matrix has the inverse `0`, as in a field with `0⁻¹ = 0`.

<?decl Matrix.inv_def?>
:::

::: mathlib
`Matrix.nonsing_inv_mul` · `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`

For `IsUnit A.det`: `A⁻¹ * A = 1`. The mirror is `Matrix.mul_nonsing_inv`. Without the hypothesis the equation can fail, since `A⁻¹ = 0` for a singular `A`.

<?decl Matrix.nonsing_inv_mul?>
:::

**Theorem (Singular matrices over a domain).** Over an integral domain, $\det A = 0$ if and only if $A v = 0$ for some $v \neq 0$.

*Proof.* Pass to the field of fractions $K$, which changes neither the determinant nor the existence of $v$: a nonzero $v$ over $K$ times a common denominator is a nonzero $v$ over $R$. Over $K$, $\det A = 0$ means that $A$ is not invertible, and by rank-nullity this means that the kernel of $A$ is not zero. $\square$

::: mathlib
`Matrix.exists_mulVec_eq_zero_iff` · `Mathlib.LinearAlgebra.Matrix.ToLinearEquiv`

The statement `(∃ v ≠ 0, M *ᵥ v = 0) ↔ M.det = 0` over an integral domain.

<?decl Matrix.exists_mulVec_eq_zero_iff?>
:::

**Theorem (Rule of Cramer).** Let $A x = b$, with $A$ an $n \times n$ matrix. Then $\det A \cdot x_i = \det A[\text{col } i := b]$ for each $i$. If $\det A$ is a unit, the system has the unique solution $x_i = \det A[\text{col } i := b] / \det A$.

*Proof.* Let $X_i$ be the identity matrix with the column $i$ replaced by $x$. The column $k$ of $A X_i$ is $A e_k$, the column $k$ of $A$, for $k \neq i$, and it is $A x = b$ for $k = i$. So $A X_i = A[\text{col } i := b]$. The expansion along the row $i$ gives $\det X_i = x_i$, since the row $i$ of $X_i$ is $x_i e_i$. By multiplicativity, $\det A[\text{col } i := b] = \det A \cdot x_i$. If $\det A$ is a unit, $A$ is invertible, so the solution exists and is unique, and the formula follows. $\square$

::: mathlib
`Matrix.mulVec_cramer` · `Mathlib.LinearAlgebra.Matrix.Adjugate`

The rule of Cramer in Mathlib: `A *ᵥ A.cramer b = A.det • b`. If `A.det` is a unit, `x = (A.det)⁻¹ • A.cramer b` solves `A *ᵥ x = b`.

<?decl Matrix.mulVec_cramer?>
:::

::: mathlib
`Matrix.cramer_eq_adjugate_mulVec` · `Mathlib.LinearAlgebra.Matrix.Adjugate`

The link of the two definitions: `A.cramer b = A.adjugate *ᵥ b`.

<?decl Matrix.cramer_eq_adjugate_mulVec?>
:::

**Definition (Determinant of an endomorphism).** Let $M$ be a free module of finite rank over $R$ and $f : M \to M$ linear. The determinant $\det f$ is $\det$ of the matrix of $f$ in a basis $b$ of $M$, used on both sides.

The definition does not depend on $b$: for another basis $b'$ with the change of basis matrix $P$, the matrix of $f$ in $b'$ is $P^{-1} A P$, by Section 2 of Chapter 3, and it has the determinant $\det A$ by the corollary above. By multiplicativity, $\det(f \circ g) = \det f \det g$.

::: mathlib
`LinearMap.det` · `Mathlib.LinearAlgebra.Determinant`

The determinant `LinearMap.det : (M →ₗ[R] M) →* R`, a monoid homomorphism. Mathlib defines it for each module: if `M` has a finite basis, it is the determinant of the matrix in a chosen basis, and otherwise it is `1`.

<?decl LinearMap.det?>
:::

::: mathlib
`LinearMap.det_toMatrix` · `Mathlib.LinearAlgebra.Determinant`

For each basis `b`: `(toMatrix b b f).det = LinearMap.det f`. This is the independence of the basis. The reverse direction is `LinearMap.det_toLin`.

<?decl LinearMap.det_toMatrix?>
:::

::: mathlib
`LinearMap.det_comp` · `Mathlib.LinearAlgebra.Determinant`

The statement `LinearMap.det (f ∘ₗ g) = LinearMap.det f * LinearMap.det g`.

<?decl LinearMap.det_comp?>
:::

### Examples

**Example (The inverse of a $2 \times 2$ matrix).** For $A = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$, the adjugate is $\begin{pmatrix} d & -b \\ -c & a \end{pmatrix}$, and $A \operatorname{adj} A = (a d - b c) I$. For $A = \begin{pmatrix} 3 & 5 \\ 1 & 2 \end{pmatrix}$ over $\mathbb{Z}$, $\det A = 1$, so $A^{-1} = \begin{pmatrix} 2 & -5 \\ -1 & 3 \end{pmatrix}$, again a matrix over $\mathbb{Z}$. For $\begin{pmatrix} 2 & 0 \\ 0 & 1 \end{pmatrix}$, the determinant $2$ is not a unit of $\mathbb{Z}$, and the matrix has no inverse over $\mathbb{Z}$, but it has one over $\mathbb{Q}$.

**Example (The rule of Cramer for a $3 \times 3$ system).** Solve
$$2x + y + 3z = 9, \qquad -y + 4z = 5, \qquad x + 2y = 4.$$
The matrix is the matrix $A$ of Section 1, with $\det A = -9$, and $b = (9, 5, 4)$. Replace the columns one at a time:
$$\det \begin{pmatrix} 9 & 1 & 3 \\ 5 & -1 & 4 \\ 4 & 2 & 0 \end{pmatrix} = 9(0 - 8) - 1(0 - 16) + 3(10 + 4) = -72 + 16 + 42 = -14,$$
$$\det \begin{pmatrix} 2 & 9 & 3 \\ 0 & 5 & 4 \\ 1 & 4 & 0 \end{pmatrix} = 2(0 - 16) - 9(0 - 4) + 3(0 - 5) = -32 + 36 - 15 = -11,$$
$$\det \begin{pmatrix} 2 & 1 & 9 \\ 0 & -1 & 5 \\ 1 & 2 & 4 \end{pmatrix} = 2(-4 - 10) - 1(0 - 5) + 9(0 + 1) = -28 + 5 + 9 = -14.$$
So $x = 14/9$, $y = 11/9$, $z = 14/9$. Check the second equation: $-11/9 + 56/9 = 45/9 = 5$. Check the third: $14/9 + 22/9 = 36/9 = 4$.

**Example (The Vandermonde determinant).** For $v_0, \dots, v_{n-1} \in R$, the Vandermonde matrix has the entries $v_i^j$. Its determinant is $\prod_{i < j} (v_j - v_i)$. For $n = 3$ and $v = (1, 2, 3)$:
$$\det \begin{pmatrix} 1 & 1 & 1 \\ 1 & 2 & 4 \\ 1 & 3 & 9 \end{pmatrix} = (2 - 1)(3 - 1)(3 - 2) = 2.$$
So the matrix is invertible over $\mathbb{Q}$ when the $v_i$ are distinct, and a polynomial of degree less than $n$ is determined by its values at $n$ distinct points.

::: mathlib
`Matrix.det_vandermonde` · `Mathlib.LinearAlgebra.Vandermonde`

The statement `(vandermonde v).det = ∏ i, ∏ j > i, (v j - v i)`, for `v : Fin n → R`. The proof is an induction that subtracts multiples of the columns.

<?decl Matrix.det_vandermonde?>
:::

**Counterexample (A left inverse in infinite dimension).** On the space of the sequences over $\mathbb{Q}$, the shift $S(a_0, a_1, \dots) = (0, a_0, a_1, \dots)$ has the left inverse $T(a_0, a_1, \dots) = (a_1, a_2, \dots)$: $T S = \mathrm{id}$. But $S T \neq \mathrm{id}$, since $S T$ sends $(1, 0, 0, \dots)$ to $0$. There is no determinant here, and the theorem on invertibility needs finite dimension.

### The library around it

The determinant of a linear map is in `Mathlib.LinearAlgebra.Determinant`, together with `LinearEquiv.det : (M ≃ₗ[R] M) →* Rˣ` and the determinant `Module.Basis.det` of a family of vectors in a basis. The adjugate is in `Mathlib.LinearAlgebra.Matrix.Adjugate`, and the inverse in `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`. Over a field, `Matrix.det_ne_zero_of_left_inverse` and `Matrix.isUnit_iff_isUnit_det` give the usual criteria.

### Exercises

1. (A) Compute the inverse of $\begin{pmatrix} 1 & 2 & 0 \\ 0 & 1 & 0 \\ 2 & 0 & 1 \end{pmatrix}$ by the adjugate.
2. (A) Solve $3x + 2y = 7$, $x + 4y = 9$ by the rule of Cramer.
3. (A) Show that $\det(A^k) = (\det A)^k$ and that $\det(A^{-1}) = (\det A)^{-1}$ for an invertible $A$.
4. (B) Find all $2 \times 2$ matrices over $\mathbb{Z}$ that are invertible over $\mathbb{Z}$ and have all entries in $\{0, 1\}$. Hint: the determinant must be $\pm 1$.
5. (B) Show that $\det(\operatorname{adj} A) = (\det A)^{n-1}$ for an $n \times n$ matrix with $\det A$ a unit. Hint: take the determinant of the adjugate identity.
6. (B) Show that an orthogonal real matrix, $Q^{\mathsf{T}} Q = I$, has $\det Q = \pm 1$.
7. (C) Show that $\det(\operatorname{adj} A) = (\det A)^{n-1}$ for each $n \times n$ matrix over a commutative ring. Hint: prove it for the matrix with indeterminate entries over $\mathbb{Z}[x_{ij}]$, whose determinant is not a zero divisor, and specialize.

### Notes and history

The multiplicativity of the determinant was proved by Cauchy and by Binet in 1812, in the general form of the formula of Cauchy and Binet. The rule of Cramer is from his book of 1750 on algebraic curves, where he used it to find a curve through given points. The method of the adjugate and the condition $\det A \neq 0$ for invertibility are in the work of Cayley on matrices in 1858.

The total inverse `A⁻¹ = Ring.inverse A.det • A.adjugate` follows the convention of Mathlib for division in a field: each operation is total, and the theorems carry the hypothesis.

### Reference

<?reference?>
