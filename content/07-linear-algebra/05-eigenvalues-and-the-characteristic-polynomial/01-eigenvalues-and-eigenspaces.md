---
title: Eigenvalues, eigenspaces and the characteristic polynomial
kind: theory
modules:
  - Mathlib.LinearAlgebra.Eigenspace.Basic
  - Mathlib.LinearAlgebra.Eigenspace.Triangularizable
  - Mathlib.LinearAlgebra.Eigenspace.Charpoly
  - Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
  - Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
  - Mathlib.LinearAlgebra.Charpoly.Basic
  - Mathlib.LinearAlgebra.Charpoly.ToMatrix
explains:
  E3: [Module.End.eigenspace, Module.End.HasEigenvalue, Module.End.eigenvectors_linearIndependent, Matrix.charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly]
  E2: [Module.End.HasEigenvector, Module.End.mem_eigenspace_iff, Module.End.hasEigenvalue_iff, Module.End.eigenspaces_iSupIndep, Module.End.exists_eigenvalue, Module.End.genEigenspace, Module.End.iSup_maxGenEigenspace_eq_top, Matrix.charmatrix, Matrix.charpoly_monic, Matrix.trace_eq_neg_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, Matrix.charpoly_fin_two, LinearMap.charpoly, LinearMap.charpoly_toMatrix]
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

## Eigenvalues, eigenspaces and the characteristic polynomial

### Overview

Let $f$ be a linear endomorphism of a vector space $V$. A scalar $\mu$ is an eigenvalue of $f$ if $f v = \mu v$ for some $v \neq 0$. The eigenvectors for $\mu$, with $0$, form the eigenspace $\ker(f - \mu)$. If $V$ has a basis of eigenvectors, the matrix of $f$ in this basis is diagonal, and $f$ is called diagonalizable.

This section defines these notions, proves that the eigenspaces for distinct eigenvalues are independent, and finds the eigenvalues of a matrix $A$ as the roots of its characteristic polynomial $\det(X I - A)$. The examples compute the eigenvalues and the eigenvectors of explicit $2 \times 2$ and $3 \times 3$ matrices, and give a matrix that is not diagonalizable and a real matrix without real eigenvalues.

### Definitions

In this section $R$ is a commutative ring, $M$ an $R$-module and $f : M \to M$ linear. Most results need $R$ to be a field.

**Definition (Eigenvalue, eigenvector, eigenspace).** For $\mu \in R$, the eigenspace of $f$ for $\mu$ is the submodule $\ker(f - \mu \cdot \mathrm{id})$. A vector $x$ is an eigenvector for $\mu$ if $x \neq 0$ and $f x = \mu x$. The scalar $\mu$ is an eigenvalue if its eigenspace is not $0$.

::: mathlib
`Module.End.eigenspace` · `Mathlib.LinearAlgebra.Eigenspace.Basic`

The eigenspace `f.eigenspace μ : Submodule R M`, for `f : Module.End R M`. It is an abbreviation for `f.genEigenspace μ 1`, the generalized eigenspace of order `1`.

<?decl Module.End.eigenspace?>
:::

::: mathlib
`Module.End.mem_eigenspace_iff` · `Mathlib.LinearAlgebra.Eigenspace.Basic`

The membership criterion `x ∈ f.eigenspace μ ↔ f x = μ • x`.

<?decl Module.End.mem_eigenspace_iff?>
:::

::: mathlib
`Module.End.HasEigenvector` · `Mathlib.LinearAlgebra.Eigenspace.Basic`

The proposition `f.HasEigenvector μ x`: `x` lies in the eigenspace for `μ` and `x ≠ 0`.

<?decl Module.End.HasEigenvector?>
:::

::: mathlib
`Module.End.HasEigenvalue` · `Mathlib.LinearAlgebra.Eigenspace.Basic`

The proposition `f.HasEigenvalue μ`: the eigenspace for `μ` is not `⊥`. Mathlib phrases it through the generalized eigenspaces, as the case of order `1`.

<?decl Module.End.HasEigenvalue?>
:::

::: mathlib
`Module.End.hasEigenvalue_iff` · `Mathlib.LinearAlgebra.Eigenspace.Basic`

The unfolding `f.HasEigenvalue μ ↔ f.eigenspace μ ≠ ⊥`. To get an eigenvector from an eigenvalue, use `Module.End.HasEigenvalue.exists_hasEigenvector`.

<?decl Module.End.hasEigenvalue_iff?>
:::

**Definition (Generalized eigenspace).** For $k \ge 1$, the generalized eigenspace of order $k$ is $\ker (f - \mu)^k$. The maximal generalized eigenspace is the union over all $k$.

::: mathlib
`Module.End.genEigenspace` · `Mathlib.LinearAlgebra.Eigenspace.Basic`

The generalized eigenspaces `f.genEigenspace μ k`, with the order `k : ℕ∞`. The order `⊤` gives the maximal one, `Module.End.maxGenEigenspace`.

<?decl Module.End.genEigenspace?>
:::

**Definition (Characteristic polynomial).** For an $n \times n$ matrix $A$ over $R$, the characteristic matrix is $X I - A$, a matrix over the polynomial ring $R[X]$. The characteristic polynomial is $\chi_A = \det(X I - A) \in R[X]$. For an endomorphism $f$ of a free module of finite rank, $\chi_f$ is $\chi_A$ for the matrix $A$ of $f$ in a basis.

The polynomial $\chi_f$ does not depend on the basis: a change of basis replaces $A$ by $P^{-1} A P$, and $X I - P^{-1} A P = P^{-1} (X I - A) P$ has the same determinant, by the multiplicativity over $R[X]$.

::: mathlib
`Matrix.charmatrix` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`

The characteristic matrix `charmatrix M : Matrix n n R[X]`, defined as `scalar n X - (C : R →+* R[X]).mapMatrix M`.

<?decl Matrix.charmatrix?>
:::

::: mathlib
`Matrix.charpoly` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`

The characteristic polynomial `M.charpoly = (charmatrix M).det`. With this sign convention it is monic.

<?decl Matrix.charpoly?>
:::

::: mathlib
`LinearMap.charpoly` · `Mathlib.LinearAlgebra.Charpoly.Basic`

The characteristic polynomial `f.charpoly` of an endomorphism of a free module of finite rank. Mathlib defines it with the basis `Module.Free.chooseBasis`, and proves the independence of the basis.

<?decl LinearMap.charpoly?>
:::

::: mathlib
`LinearMap.charpoly_toMatrix` · `Mathlib.LinearAlgebra.Charpoly.ToMatrix`

The independence of the basis: `(toMatrix b b f).charpoly = f.charpoly` for each finite basis `b`.

<?decl LinearMap.charpoly_toMatrix?>
:::

### Theorems and proofs

**Theorem (Independence of eigenvectors).** Let $R$ be a field. If $x_1, \dots, x_k$ are eigenvectors of $f$ for pairwise distinct eigenvalues $\mu_1, \dots, \mu_k$, then $x_1, \dots, x_k$ are linearly independent.

*Proof.* Induction on $k$. For $k = 1$, $x_1 \neq 0$ is independent. For the step, suppose $\sum_{i=1}^k c_i x_i = 0$. Apply $f$, and subtract $\mu_k$ times the original relation:
$$\sum_{i=1}^{k} c_i (\mu_i - \mu_k) x_i = 0.$$
The term with $i = k$ is zero. By the induction hypothesis on $x_1, \dots, x_{k-1}$, $c_i (\mu_i - \mu_k) = 0$ for $i < k$. Since $\mu_i \neq \mu_k$, $c_i = 0$ for $i < k$. Then $c_k x_k = 0$ and $x_k \neq 0$ give $c_k = 0$. $\square$

**Corollary (Diagonalization).** An endomorphism of a space of dimension $n$ has at most $n$ eigenvalues. If it has $n$ distinct eigenvalues, it is diagonalizable.

*Proof.* Eigenvectors for distinct eigenvalues are independent, and an independent family has at most $n$ elements. If there are $n$ distinct eigenvalues, the $n$ eigenvectors form a basis. $\square$

::: mathlib
`Module.End.eigenvectors_linearIndependent` · `Mathlib.LinearAlgebra.Eigenspace.Basic`

For a set `μs` of eigenvalues and eigenvectors `xs μ` for each `μ ∈ μs`, the family `xs` is linearly independent. It holds over a domain with a torsion free module, which includes each vector space.

<?decl Module.End.eigenvectors_linearIndependent?>
:::

::: mathlib
`Module.End.eigenspaces_iSupIndep` · `Mathlib.LinearAlgebra.Eigenspace.Basic`

The stronger form: the eigenspaces are independent as submodules, `iSupIndep f.eigenspace`. Each eigenspace meets the sum of the others only in `0`.

<?decl Module.End.eigenspaces_iSupIndep?>
:::

**Theorem (Eigenvalues are the roots of $\chi$).** Let $R$ be a field and $A$ an $n \times n$ matrix. Then $\mu$ is an eigenvalue of $A$ if and only if $\chi_A(\mu) = 0$.

*Proof.* Evaluation at $\mu$ is a ring homomorphism $R[X] \to R$, and the determinant is a polynomial in the entries, so $\chi_A(\mu) = \det(\mu I - A)$. By Section 2 of Chapter 4, $\det(\mu I - A) = 0$ if and only if $(\mu I - A) v = 0$ for some $v \neq 0$, that is, $A v = \mu v$. $\square$

::: mathlib
`Module.End.hasEigenvalue_iff_isRoot_charpoly` · `Mathlib.LinearAlgebra.Eigenspace.Charpoly`

The statement `f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ`, over a domain, for a free module of finite rank.

<?decl Module.End.hasEigenvalue_iff_isRoot_charpoly?>
:::

**Theorem (Coefficients).** $\chi_A$ is monic of degree $n$. Its coefficient of $X^{n-1}$ is $-\operatorname{tr} A$, and its constant coefficient is $(-1)^n \det A$. For $n = 2$:
$$\chi_A = X^2 - (\operatorname{tr} A) X + \det A.$$

*Proof.* In the formula of Leibniz for $\det(X I - A)$, the identity permutation gives $\prod_i (X - A_{ii})$. Each other permutation moves at least two indices, so its term contains at most $n - 2$ diagonal factors and has degree at most $n - 2$. So the coefficients of $X^n$ and $X^{n-1}$ come from $\prod_i (X - A_{ii}) = X^n - (\sum_i A_{ii}) X^{n-1} + \dots$. The constant coefficient is $\chi_A(0) = \det(-A) = (-1)^n \det A$. For $n = 2$ this gives all three coefficients. $\square$

::: mathlib
`Matrix.charpoly_monic` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`

The statement `M.charpoly.Monic`. The degree is `Matrix.charpoly_natDegree_eq_dim`: `M.charpoly.natDegree = Fintype.card n`, over a nontrivial ring.

<?decl Matrix.charpoly_monic?>
:::

::: mathlib
`Matrix.trace_eq_neg_charpoly_coeff` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`

The statement `M.trace = -M.charpoly.coeff (Fintype.card n - 1)`.

<?decl Matrix.trace_eq_neg_charpoly_coeff?>
:::

::: mathlib
`Matrix.det_eq_sign_charpoly_coeff` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`

The statement `M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0`.

<?decl Matrix.det_eq_sign_charpoly_coeff?>
:::

::: mathlib
`Matrix.charpoly_fin_two` · `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`

The $2 \times 2$ formula `M.charpoly = X ^ 2 - C M.trace * X + C M.det`.

<?decl Matrix.charpoly_fin_two?>
:::

**Theorem (Existence of an eigenvalue).** Over an algebraically closed field, each endomorphism of a nonzero space of finite dimension has an eigenvalue. Also, the space is the sum of the maximal generalized eigenspaces.

*Proof of the first claim.* $\chi_f$ has the degree $n \ge 1$, so it has a root. The root is an eigenvalue. $\square$

The second claim is the first step towards the normal form of Jordan. Its proof uses the minimal polynomial and is in Mathlib; it is not given here.

::: mathlib
`Module.End.exists_eigenvalue` · `Mathlib.LinearAlgebra.Eigenspace.Triangularizable`

The statement `∃ c, f.HasEigenvalue c`, for an algebraically closed field and a nontrivial space of finite dimension.

<?decl Module.End.exists_eigenvalue?>
:::

::: mathlib
`Module.End.iSup_maxGenEigenspace_eq_top` · `Mathlib.LinearAlgebra.Eigenspace.Triangularizable`

The statement `⨆ μ, f.maxGenEigenspace μ = ⊤` over an algebraically closed field. With the independence of the generalized eigenspaces it gives the direct sum decomposition.

<?decl Module.End.iSup_maxGenEigenspace_eq_top?>
:::

### Examples

**Example (A symmetric $2 \times 2$ matrix).** Let $A = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ over $\mathbb{Q}$. Then $\operatorname{tr} A = 4$, $\det A = 3$, and $\chi_A = X^2 - 4X + 3 = (X - 1)(X - 3)$. For $\mu = 3$: $A - 3I = \begin{pmatrix} -1 & 1 \\ 1 & -1 \end{pmatrix}$, with the kernel spanned by $(1, 1)$. For $\mu = 1$: $A - I = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$, with the kernel spanned by $(1, -1)$. With $P = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$, $P^{-1} A P = \begin{pmatrix} 3 & 0 \\ 0 & 1 \end{pmatrix}$. So $A^k = P \operatorname{diag}(3^k, 1) P^{-1}$, and $(A^k)_{11} = (3^k + 1)/2$.

**Example (A rotation).** Let $J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$, the rotation by a right angle. Then $\chi_J = X^2 + 1$. Over $\mathbb{R}$ it has no root, and $J$ has no eigenvalue: no line through $0$ is fixed by a rotation by a right angle. Over $\mathbb{C}$ the eigenvalues are $i$ and $-i$, with the eigenvectors $(1, -i)$ and $(1, i)$: $J (1, -i) = (i, 1) = i (1, -i)$.

**Example (A matrix that is not diagonalizable).** Let $N = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$. Then $\chi_N = (X - 1)^2$, and $1$ is the only eigenvalue. The eigenspace is the kernel of $N - I = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$, the line spanned by $(1, 0)$. So there is no basis of eigenvectors. The generalized eigenspace of order $2$ is $\ker (N - I)^2 = \ker 0 = \mathbb{Q}^2$.

**Example (A $3 \times 3$ matrix).** Let
$$A = \begin{pmatrix} 2 & 0 & 0 \\ 1 & 3 & 0 \\ 4 & 5 & 3 \end{pmatrix}.$$
The matrix $X I - A$ is lower triangular, so $\chi_A = (X - 2)(X - 3)^2$. For $\mu = 2$: $A - 2I$ has the rows $(0, 0, 0)$, $(1, 1, 0)$, $(4, 5, 1)$, and its kernel is spanned by $(1, -1, 1)$. Check: $A(1, -1, 1) = (2, -2, 2)$. For $\mu = 3$: $A - 3I$ has the rows $(-1, 0, 0)$, $(1, 0, 0)$, $(4, 5, 0)$, of rank $2$, and its kernel is spanned by $(0, 0, 1)$. The eigenvalue $3$ is a double root of $\chi_A$ with an eigenspace of dimension $1$, so $A$ is not diagonalizable. Also $\operatorname{tr} A = 8 = 2 + 3 + 3$ and $\det A = 18 = 2 \cdot 3 \cdot 3$.

**Counterexample (Eigenvectors of a sum).** Eigenvalues do not add. For $A = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ and $B = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$, both have only the eigenvalue $0$, but $A + B = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ has the eigenvalues $1$ and $-1$.

### The library around it

The eigenspaces are in `Mathlib.LinearAlgebra.Eigenspace.Basic`, and the results over an algebraically closed field are in `Mathlib.LinearAlgebra.Eigenspace.Triangularizable`. A matrix `A` has eigenvalues through its linear map `Matrix.toLin' A`. The spectrum of an element of an algebra, `spectrum R a`, is a related notion for operators on infinite dimensional spaces, and `Module.End.hasEigenvalue_iff_mem_spectrum` connects the two in finite dimension. The semisimple and diagonalizable endomorphisms are in `Mathlib.LinearAlgebra.Semisimple`.

Common errors of a learner:

- `Matrix.charpoly` is `det(X I - A)`, which is monic. Some books use `det(A - X I)`, which differs by the sign $(-1)^n$.
- `f.HasEigenvalue μ` is a statement about a submodule, not about a polynomial. The bridge to the roots of $\chi_f$ needs the hypotheses of `hasEigenvalue_iff_isRoot_charpoly`: a domain and a free module of finite rank.

### Exercises

1. (A) Find the eigenvalues and the eigenvectors of $\begin{pmatrix} 4 & 1 \\ 2 & 3 \end{pmatrix}$ over $\mathbb{Q}$.
2. (A) Show that $0$ is an eigenvalue of $A$ if and only if $A$ is singular.
3. (A) Show that a nilpotent matrix, $A^k = 0$, has only the eigenvalue $0$. Hint: apply $A^k$ to an eigenvector.
4. (B) Show that $\chi_{A B} = \chi_{B A}$ for square matrices $A$ and $B$ with $A$ invertible. Hint: $B A = A^{-1} (A B) A$. Mathlib proves it for all square matrices as `Matrix.charpoly_mul_comm`.
5. (B) Diagonalize $\begin{pmatrix} 1 & 2 \\ 2 & 1 \end{pmatrix}$ and compute its $k$-th power.
6. (B) Show that the eigenvalues of a real symmetric $2 \times 2$ matrix are real. Hint: the discriminant of $\chi_A$ is $(a - d)^2 + 4 b^2$.
7. (C) Let $A$ be the $n \times n$ matrix of the cyclic shift, $A e_i = e_{i+1}$ with $e_{n+1} = e_1$. Show that $\chi_A = X^n - 1$, and find the eigenvectors over $\mathbb{C}$. Hint: use the vectors $(1, \zeta, \zeta^2, \dots)$ for an $n$-th root of unity $\zeta$.

### Notes and history

Eigenvalues appeared in the eighteenth century, in the work of Euler and Lagrange on the axes of rotating bodies and on small oscillations. Cauchy proved in 1829 that a real symmetric matrix has real eigenvalues. The word eigenvalue is a half translation of the German Eigenwert, from the work of Hilbert on integral equations around 1904. The characteristic polynomial appears in the work of Cauchy and of Sylvester, who also used the word "latent roots".

The definition of the eigenspace as the generalized eigenspace of order $1$ lets the two theories share their lemmas.

### Reference

<?reference?>
