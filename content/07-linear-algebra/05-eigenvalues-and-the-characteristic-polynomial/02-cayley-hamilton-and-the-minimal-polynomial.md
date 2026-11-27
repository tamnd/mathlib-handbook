---
title: The theorem of Cayley and Hamilton and the minimal polynomial
kind: theory
modules:
  - Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
  - Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
  - Mathlib.LinearAlgebra.Eigenspace.Minpoly
  - Mathlib.LinearAlgebra.JordanChevalley
explains:
  E3: [Matrix.aeval_self_charpoly, LinearMap.aeval_self_charpoly, Module.End.hasEigenvalue_iff_isRoot]
  E2: [Matrix.minpoly_dvd_charpoly, LinearMap.minpoly_dvd_charpoly, Module.End.exists_isNilpotent_isSemisimple, Matrix.trace_eq_sum_roots_charpoly, Matrix.det_eq_prod_roots_charpoly]
  E1: auto
families: []
requires: [V07.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The theorem of Cayley and Hamilton and the minimal polynomial

### Overview

A square matrix $A$ can be put into a polynomial: for $p = \sum_k c_k X^k$, the matrix $p(A)$ is $\sum_k c_k A^k$. The theorem of Cayley and Hamilton says that $A$ is a root of its own characteristic polynomial: $\chi_A(A) = 0$. It holds over each commutative ring. The polynomials $p$ with $p(A) = 0$ form an ideal of $R[X]$, and over a field its monic generator is the minimal polynomial $m_A$. The theorem gives $m_A \mid \chi_A$, and the two polynomials have the same roots.

This section proves the theorem by the adjugate identity of Chapter 4, relates the minimal polynomial to the eigenvalues, and states the decomposition of Jordan and Chevalley. The examples verify the theorem for a $2 \times 2$ matrix, use it to compute an inverse and a power, and compare $m_A$ with $\chi_A$.

### Definitions

**Definition (Evaluation at a matrix).** For $p = \sum_k c_k X^k \in R[X]$ and an $n \times n$ matrix $A$, $p(A) = \sum_k c_k A^k$, with $A^0 = I$. The map $p \mapsto p(A)$ is a homomorphism of $R$-algebras $R[X] \to M_n(R)$. Its image is commutative, since all the powers of $A$ commute.

::: mathlib
`Polynomial.aeval` · `Mathlib.Algebra.Polynomial.AlgebraMap`

The evaluation `aeval x : R[X] →ₐ[R] A` at an element `x` of an `R`-algebra `A`. For a matrix, `aeval M p` is `p(M)`. For an endomorphism, `aeval f p` is `p(f)`. The polynomials of Mathlib are treated in Volume 6.

<?decl Polynomial.aeval?>
:::

**Definition (Minimal polynomial).** Let $K$ be a field and $A$ an $n \times n$ matrix over $K$. The minimal polynomial $m_A$ is the monic polynomial of the least degree with $m_A(A) = 0$.

It exists, since the $n^2 + 1$ matrices $I, A, \dots, A^{n^2}$ are dependent in the space $M_n(K)$ of dimension $n^2$. It is unique, and it divides each $p$ with $p(A) = 0$: divide $p = q m_A + r$ with $\deg r < \deg m_A$; then $r(A) = 0$, so $r = 0$ by the minimality.

::: mathlib
`minpoly` · `Mathlib.FieldTheory.Minpoly.Basic`

The minimal polynomial `minpoly R x` of an element `x` of an `R`-algebra. It is `0` if `x` is not integral. Its home is the field theory of Volume 11. The two facts above are `minpoly.aeval` and `minpoly.dvd`.

<?decl minpoly?>
:::

### Theorems and proofs

**Theorem (Cayley and Hamilton).** For each $n \times n$ matrix $A$ over a commutative ring $R$, $\chi_A(A) = 0$.

*Proof.* Work in the ring $M_n(R[X])$ of the matrices with polynomial entries. By the adjugate identity of Chapter 4, applied to the matrix $X I - A$ over the commutative ring $R[X]$,
$$\operatorname{adj}(X I - A) \cdot (X I - A) = \chi_A \cdot I. \qquad (1)$$
Each entry of $\operatorname{adj}(X I - A)$ is a minor of size $n - 1$, a polynomial of degree at most $n - 1$. Collect the coefficients of each power of $X$ into a matrix:
$$\operatorname{adj}(X I - A) = \sum_{k=0}^{n-1} B_k X^k, \qquad B_k \in M_n(R).$$
Write $\chi_A = \sum_{k=0}^n c_k X^k$, with $c_n = 1$. A matrix with polynomial entries is a polynomial with matrix coefficients, and the variable $X$ commutes with each matrix, since it is a scalar. So (1) becomes an identity of polynomials with coefficients in $M_n(R)$:
$$\Bigl(\sum_{k=0}^{n-1} B_k X^k\Bigr) (X I - A) = \sum_{k=0}^n c_k I X^k.$$
Compare the coefficients of $X^k$ for $k = 0, \dots, n$. With the conventions $B_{-1} = 0$ and $B_n = 0$:
$$B_{k-1} - B_k A = c_k I \qquad (0 \le k \le n). \qquad (2)$$
Multiply the equation (2) for $k$ on the right by $A^k$, and sum over $k$:
$$\sum_{k=0}^n \bigl(B_{k-1} A^k - B_k A^{k+1}\bigr) = \sum_{k=0}^n c_k A^k = \chi_A(A).$$
The left side telescopes: the term $B_k A^{k+1}$ with the sign $-$ in the summand $k$ cancels the term $B_k A^{k+1}$ with the sign $+$ in the summand $k + 1$. What remains is $B_{-1} A^0 - B_n A^{n+1} = 0$. So $\chi_A(A) = 0$. $\square$

The naive proof "substitute $X = A$ in $\det(X I - A)$, to get $\det(A - A) = 0$" is wrong: it gives the scalar $\det 0$, not the matrix $\chi_A(A)$. The substitution of a matrix into a polynomial with matrix coefficients is not multiplicative in general, since the coefficients do not commute with $A$. The proof above avoids the problem: it places $A$ on the right in each step, and the telescoping is a direct computation.

::: mathlib
`Matrix.aeval_self_charpoly` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`

The theorem of Cayley and Hamilton: `aeval M M.charpoly = 0`. The proof in Mathlib follows the same plan. It starts from `adjugate_mul` for `charmatrix M`, transports the identity along the isomorphism `matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X]`, and evaluates at `M` on the right with `Polynomial.eval_mul_X_sub_C`, which says that `p * (X - C r)` vanishes at `r`.

<?decl Matrix.aeval_self_charpoly?>
:::

::: mathlib
`matPolyEquiv` · `Mathlib.RingTheory.MatrixPolynomialAlgebra`

The algebra isomorphism between the matrices of polynomials and the polynomials with matrix coefficients. It is the formal version of the step "collect the coefficients into a matrix".

<?decl matPolyEquiv?>
:::

::: mathlib
`LinearMap.aeval_self_charpoly` · `Mathlib.LinearAlgebra.Charpoly.Basic`

The version for an endomorphism of a free module of finite rank: `aeval f f.charpoly = 0`. It follows from the matrix version through `LinearMap.toMatrix`, which is an algebra isomorphism.

<?decl LinearMap.aeval_self_charpoly?>
:::

**Corollary (Minimal polynomial divides $\chi$).** Over a field, $m_A \mid \chi_A$. In particular, $\deg m_A \le n$.

*Proof.* $\chi_A(A) = 0$, and $m_A$ divides each polynomial that vanishes at $A$. $\square$

::: mathlib
`Matrix.minpoly_dvd_charpoly` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly`

The statement `minpoly K M ∣ M.charpoly` over a field.

<?decl Matrix.minpoly_dvd_charpoly?>
:::

::: mathlib
`LinearMap.minpoly_dvd_charpoly` · `Mathlib.LinearAlgebra.Charpoly.Basic`

The same for an endomorphism of a space of finite dimension: `minpoly K f ∣ f.charpoly`.

<?decl LinearMap.minpoly_dvd_charpoly?>
:::

**Theorem (Roots of the minimal polynomial).** Over a field, $\mu$ is an eigenvalue of $f$ if and only if $m_f(\mu) = 0$. So $m_f$ and $\chi_f$ have the same roots.

*Proof.* Let $f v = \mu v$ with $v \neq 0$. Then $f^k v = \mu^k v$, so $p(f) v = p(\mu) v$ for each polynomial $p$. With $p = m_f$: $0 = m_f(\mu) v$, so $m_f(\mu) = 0$. Conversely, let $m_f(\mu) = 0$, and write $m_f = (X - \mu) q$. Since $\deg q < \deg m_f$, $q(f) \neq 0$, so $w = q(f) u \neq 0$ for some $u$. Then $(f - \mu) w = m_f(f) u = 0$, so $w$ is an eigenvector for $\mu$. $\square$

::: mathlib
`Module.End.hasEigenvalue_iff_isRoot` · `Mathlib.LinearAlgebra.Eigenspace.Minpoly`

The statement `f.HasEigenvalue μ ↔ (minpoly R f).IsRoot μ`. The two directions are `Module.End.hasEigenvalue_of_isRoot` and `Module.End.isRoot_of_hasEigenvalue`.

<?decl Module.End.hasEigenvalue_iff_isRoot?>
:::

**Theorem (Trace and determinant from the eigenvalues).** Over an algebraically closed field, $\chi_A = \prod_{i=1}^n (X - \lambda_i)$, with the eigenvalues $\lambda_i$ repeated by their multiplicity as roots. So $\operatorname{tr} A = \sum_i \lambda_i$ and $\det A = \prod_i \lambda_i$.

*Proof.* A monic polynomial over an algebraically closed field is the product of the factors $X - \lambda$ over its roots. Compare the coefficients of $X^{n-1}$ and $X^0$ with Section 1: $-\operatorname{tr} A = -\sum \lambda_i$, and $(-1)^n \det A = (-1)^n \prod \lambda_i$. $\square$

::: mathlib
`Matrix.trace_eq_sum_roots_charpoly` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs`

The statement `A.trace = A.charpoly.roots.sum` over an algebraically closed field. The roots form a multiset, so the multiplicities count.

<?decl Matrix.trace_eq_sum_roots_charpoly?>
:::

::: mathlib
`Matrix.det_eq_prod_roots_charpoly` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs`

The statement `A.det = A.charpoly.roots.prod`.

<?decl Matrix.det_eq_prod_roots_charpoly?>
:::

**Theorem (Jordan and Chevalley).** Let $K$ be a perfect field, for example a field of characteristic $0$ or a finite field, and $f$ an endomorphism of a space of finite dimension over $K$. Then $f = n + s$, with $n$ nilpotent, $s$ semisimple, and both $n$ and $s$ polynomials in $f$. In particular $n$ and $s$ commute.

The proof is not given here. Over an algebraically closed field, $s$ acts on each maximal generalized eigenspace for $\mu$ as $\mu$, and $n = f - s$. Semisimple means that each invariant subspace has an invariant complement; over an algebraically closed field it means diagonalizable.

::: mathlib
`Module.End.exists_isNilpotent_isSemisimple` · `Mathlib.LinearAlgebra.JordanChevalley`

The decomposition of Jordan and Chevalley: `∃ n ∈ K[f], ∃ s ∈ K[f], IsNilpotent n ∧ s.IsSemisimple ∧ f = n + s`, for a perfect field. Here `K[f]` is the subalgebra generated by `f`, the polynomials in `f`. At this commit, Mathlib states no normal form of Jordan for matrices; this decomposition and the generalized eigenspaces do its work.

<?decl Module.End.exists_isNilpotent_isSemisimple?>
:::

### Examples

**Example (Cayley and Hamilton for a $2 \times 2$ matrix).** Let $A = \begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$. Then $\operatorname{tr} A = 5$ and $\det A = -2$, so $\chi_A = X^2 - 5X - 2$. Compute:
$$A^2 = \begin{pmatrix} 7 & 10 \\ 15 & 22 \end{pmatrix}, \qquad A^2 - 5A - 2I = \begin{pmatrix} 7 - 5 - 2 & 10 - 10 \\ 15 - 15 & 22 - 20 - 2 \end{pmatrix} = 0.$$
For a general $2 \times 2$ matrix the theorem is the identity $A^2 - (a + d) A + (a d - b c) I = 0$, which a direct computation of the four entries verifies.

**Example (An inverse from the theorem).** For the same $A$, the theorem gives $A (A - 5I) = 2I$. So $A^{-1} = \tfrac{1}{2}(A - 5I) = \tfrac{1}{2}\begin{pmatrix} -4 & 2 \\ 3 & -1 \end{pmatrix}$. In general, if $\chi_A = X^n + \dots + c_1 X + c_0$ with $c_0 = (-1)^n \det A$ a unit, then $A^{-1} = -c_0^{-1}(A^{n-1} + c_{n-1} A^{n-2} + \dots + c_1 I)$, a polynomial in $A$.

**Example (Minimal and characteristic polynomials compared).** Over $\mathbb{Q}$:

- For $I_2$: $\chi = (X - 1)^2$ and $m = X - 1$.
- For $N = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$: $\chi = (X - 1)^2$, and $N - I \neq 0$, so $m = (X - 1)^2$.
- For $D = \operatorname{diag}(2, 2, 3)$: $\chi = (X - 2)^2 (X - 3)$ and $m = (X - 2)(X - 3)$, since $(D - 2I)(D - 3I) = \operatorname{diag}(0, 0, 1) \operatorname{diag}(-1, -1, 0) = 0$.
- For the matrix $A$ of the $3 \times 3$ example of Section 1, with $\chi_A = (X - 2)(X - 3)^2$: $m_A$ has both roots $2$ and $3$. The product is $(A - 2I)(A - 3I) = \begin{pmatrix} 0 & 0 & 0 \\ 0 & 0 & 0 \\ 5 & 5 & 0 \end{pmatrix} \neq 0$, so $m_A = \chi_A$.

The matrices $I_2$ and $N$ have the same $\chi$ but different $m$, and they are not similar. A matrix over a field is diagonalizable if and only if its minimal polynomial is a product of distinct linear factors. So $D$ is diagonalizable and $N$ is not.

**Example (The decomposition of Jordan and Chevalley).** For $N = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$, $s = I$ and $n = N - I = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. Here $n^2 = 0$, $s$ is diagonal, and both are polynomials in $N$: $s = 1$ and $n = N - 1$. For $M = \begin{pmatrix} 2 & 1 \\ 0 & 3 \end{pmatrix}$, with distinct eigenvalues, $M$ is diagonalizable, so $s = M$ and $n = 0$. The naive split of $M$ into its diagonal and its strictly upper part is not the decomposition: $\begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ does not commute with $\operatorname{diag}(2, 3)$.

### The library around it

The proof of the theorem is in `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`, the relation to the minimal polynomial is in `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly` and `Mathlib.LinearAlgebra.Eigenspace.Minpoly`, and the decomposition is in `Mathlib.LinearAlgebra.JordanChevalley`. The lemma `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent` and the file `Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField` treat the characteristic polynomial in characteristic $p$, where $\chi_{A^p} = \chi_A$ over $\mathbb{F}_p$.

### Exercises

1. (A) Verify the theorem of Cayley and Hamilton for $\begin{pmatrix} 0 & 1 \\ -6 & 5 \end{pmatrix}$, and use it to compute $A^{-1}$.
2. (A) Find the minimal polynomial of $\begin{pmatrix} 3 & 0 & 0 \\ 0 & 3 & 1 \\ 0 & 0 & 3 \end{pmatrix}$.
3. (A) Show that a matrix with $A^2 = A$ has the minimal polynomial $X$, $X - 1$ or $X^2 - X$, and is diagonalizable.
4. (B) Use the theorem to show that a nilpotent $n \times n$ matrix over a field satisfies $A^n = 0$. Hint: $\chi_A = X^n$ by the roots of $m_A$.
5. (B) Verify the theorem for a general $3 \times 3$ upper triangular matrix by a direct computation of $(A - a_{11} I)(A - a_{22} I)(A - a_{33} I)$.
6. (B) For $A = \begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$, compute $A^5$ by the relation $A^2 = 5A + 2I$.
7. (C) Prove the theorem of Cayley and Hamilton for a diagonalizable matrix over a field directly, and deduce it for each complex matrix by the density of the diagonalizable matrices. Explain why this argument does not work over $\mathbb{F}_2$.

### Notes and history

Cayley stated the theorem in his memoir on matrices of 1858, verified it for $2 \times 2$ matrices, and wrote that he had verified it for $3 \times 3$ matrices. Hamilton had proved a version for the quaternions, which act on a space of dimension $4$, in 1853. Frobenius gave the first general proof in 1878 and introduced the minimal polynomial. Jordan published his normal form in 1870, and Chevalley formulated the additive decomposition for algebraic groups in the 1950s.

The proof by the isomorphism `matPolyEquiv` replaces the informal step "substitute $A$ for $X$" by a computation that the kernel of Lean checks.

### Reference

<?reference?>
