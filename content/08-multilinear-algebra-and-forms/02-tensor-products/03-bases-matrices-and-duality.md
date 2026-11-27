---
title: Bases, matrices and duality
kind: theory
modules:
  - Mathlib.LinearAlgebra.TensorProduct.Basis
  - Mathlib.LinearAlgebra.TensorProduct.Free
  - Mathlib.LinearAlgebra.TensorProduct.Matrix
  - Mathlib.LinearAlgebra.TensorProduct.Finiteness
  - Mathlib.LinearAlgebra.Contraction
  - Mathlib.LinearAlgebra.Coevaluation
  - Mathlib.LinearAlgebra.DirectSum.Finsupp
explains:
  E3: [Module.Basis.tensorProduct, TensorProduct.toMatrix_map, dualTensorHom]
  E2: [Module.Basis.tensorProduct_apply, Module.Free.tensor, TensorProduct.equivFinsuppOfBasisRight, finsuppTensorFinsupp, TensorProduct.exists_finset, Matrix.toLin_kronecker, dualTensorHom_apply, dualTensorHomEquiv, contractLeft, contractLeft_apply, coevaluation, coevaluation_apply_one]
  E1: auto
families: []
requires: [V08.C01, V07.C02, V07.C03, V07.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bases, matrices and duality

### Overview

If $M$ has a basis $(e_i)$ and $N$ a basis $(f_j)$, then $M \otimes N$ has the basis $(e_i \otimes f_j)$. So the elements of $R^m \otimes R^n$ are the $m \times n$ matrices, and the least number of pure tensors in a sum is the rank of the matrix. The tensor product $f \otimes g$ of two linear maps has the Kronecker product of their matrices as its matrix. For a finite free module $M$, the tensor product $M^* \otimes N$ is the module $\operatorname{Hom}(M, N)$, and the trace of an endomorphism is the contraction $\varphi \otimes m \mapsto \varphi(m)$. The section uses Sections 1 and 2 of this chapter and Volume 7, Chapters 2, 3 and 6.

### Definitions

Fix a commutative ring $R$. All tensor products are over $R$.

**Definition (Rank of a tensor).** The rank of an element $t \in M \otimes N$ is the least $r \ge 0$ such that $t = \sum_{k=1}^{r} x_k \otimes y_k$ for some $x_k \in M$ and $y_k \in N$.

By Section 1 each element is a finite sum of pure tensors, so the rank exists. The elements of rank at most $1$ are the pure tensors.

**Definition (Contraction).** The contraction is the linear map $c : M^* \otimes M \to R$ with $c(\varphi \otimes m) = \varphi(m)$. It exists because the evaluation $(\varphi, m) \mapsto \varphi(m)$ is bilinear.

**Definition (The map to Hom).** Let $\Theta : M^* \otimes N \to \operatorname{Hom}(M, N)$ be the linear map with $\Theta(\varphi \otimes n)(m) = \varphi(m) \, n$. It exists because $(\varphi, n) \mapsto (m \mapsto \varphi(m) n)$ is bilinear.

::: mathlib
`dualTensorHom` · `Mathlib.LinearAlgebra.Contraction`

The map `dualTensorHom R M N : Module.Dual R M ⊗[R] N →ₗ[R] M →ₗ[R] N`, with `dualTensorHom_apply` for the value `f m • n`. The contraction is `contractLeft R M : Module.Dual R M ⊗[R] M →ₗ[R] R`, with `contractLeft_apply`.

<?decl dualTensorHom?>
:::

### Theorems and proofs

**Theorem (Basis of a tensor product).** Let $M$ and $N$ be free with bases $(e_i)_{i \in I}$ and $(f_j)_{j \in J}$. Then $(e_i \otimes f_j)_{(i, j) \in I \times J}$ is a basis of $M \otimes N$.

*Proof.* Spanning. Write $m = \sum_i a_i e_i$ and $n = \sum_j b_j f_j$. Then $m \otimes n = \sum_{i, j} a_i b_j \, e_i \otimes f_j$. The pure tensors span $M \otimes N$, so the $e_i \otimes f_j$ span too.

Independence. Let $x_k : M \to R$ and $y_l : N \to R$ be the coordinate functions. The map $(m, n) \mapsto x_k(m) \, y_l(n)$ is bilinear, so it induces a linear map $\beta_{k l} : M \otimes N \to R$ with $\beta_{k l}(e_i \otimes f_j) = 1$ for $(i, j) = (k, l)$ and $0$ otherwise. If a finite sum $\sum_{i, j} c_{i j} \, e_i \otimes f_j$ is $0$, apply $\beta_{k l}$: it gives $c_{k l} = 0$. $\square$

**Corollary (Dimension).** If $M$ and $N$ are free of finite ranks $m$ and $n$, then $M \otimes N$ is free of rank $m n$. Over a field, $\dim (V \otimes W) = \dim V \cdot \dim W$.

::: mathlib
`Module.Basis.tensorProduct` · `Mathlib.LinearAlgebra.TensorProduct.Basis`

From bases `b : Basis ι R M` and `c : Basis κ R N`, the basis `b.tensorProduct c : Basis (ι × κ) R (M ⊗[R] N)`, with `Module.Basis.tensorProduct_apply` for `b i ⊗ₜ c j`. The instance `Module.Free.tensor` says that a tensor product of free modules is free. The Mathlib proof goes through `finsuppTensorFinsupp`, the isomorphism $R^{(I)} \otimes R^{(J)} \cong R^{(I \times J)}$. Over a field, `Module.finrank_tensorProduct` gives the dimension. With a basis of one factor only, `TensorProduct.equivFinsuppOfBasisRight` writes $M \otimes N \cong M^{(\kappa)}$.

<?decl Module.Basis.tensorProduct?>
:::

**Proposition (Tensors are matrices).** The linear map $\Phi : R^m \otimes R^n \to M_{m \times n}(R)$ with $\Phi(x \otimes y) = x y^{\mathsf{T}}$ is an isomorphism. It sends $e_i \otimes f_j$ to the matrix unit $E_{i j}$, so $\Phi(\sum c_{i j} \, e_i \otimes f_j) = (c_{i j})$.

*Proof.* The map $(x, y) \mapsto x y^{\mathsf{T}}$ is bilinear, which gives $\Phi$. The matrix $e_i f_j^{\mathsf{T}}$ has $1$ at $(i, j)$ and $0$ elsewhere, so $\Phi$ sends the basis $(e_i \otimes f_j)$ of the theorem to the basis $(E_{i j})$ of the matrices. A linear map that sends a basis to a basis is an isomorphism. $\square$

**Theorem (Rank of a tensor).** Over a field $K$, the rank of $t \in K^m \otimes K^n$ equals the rank of the matrix $\Phi(t)$.

*Proof.* If $t = \sum_{k=1}^{r} x_k \otimes y_k$, then $\Phi(t) = \sum_k x_k y_k^{\mathsf{T}} = X Y^{\mathsf{T}}$, where $X$ is the $m \times r$ matrix with the columns $x_k$ and $Y$ the $n \times r$ matrix with the columns $y_k$. So $\operatorname{rank} \Phi(t) \le r$. Conversely, let $C = \Phi(t)$ have rank $r$, and let $x_1, \dots, x_r$ be a basis of its column space. Each column of $C$ is a combination of the $x_k$, so $C = X B$ for an $r \times n$ matrix $B$. Let $y_k$ be the row $k$ of $B$, as a column vector. Then $C = \sum_k x_k y_k^{\mathsf{T}} = \Phi(\sum_k x_k \otimes y_k)$, and since $\Phi$ is injective, $t$ is a sum of $r$ pure tensors. $\square$

**Theorem (Kronecker product).** Let $f : M \to M'$ and $g : N \to N'$ be linear maps between finite free modules, with matrices $A$ and $B$ in bases $(e_j)$, $(e'_i)$, $(f_l)$, $(f'_k)$. In the bases $(e_j \otimes f_l)$ and $(e'_i \otimes f'_k)$, the matrix of $f \otimes g$ has the entry $A_{i j} B_{k l}$ in the row $(i, k)$ and the column $(j, l)$.

*Proof.* $(f \otimes g)(e_j \otimes f_l) = f(e_j) \otimes g(f_l) = \big(\sum_i A_{i j} e'_i\big) \otimes \big(\sum_k B_{k l} f'_k\big) = \sum_{i, k} A_{i j} B_{k l} \, e'_i \otimes f'_k$. $\square$

This matrix is the Kronecker product $A \otimes B$. When the pairs are ordered with the first index first, it is the block matrix $(A_{i j} B)_{i, j}$.

::: mathlib
`TensorProduct.toMatrix_map` · `Mathlib.LinearAlgebra.TensorProduct.Matrix`

The statement `toMatrix (bM.tensorProduct bN) (bM'.tensorProduct bN') (TensorProduct.map f g) = toMatrix bM bM' f ⊗ₖ toMatrix bN bN' g`. Rows and columns are indexed by pairs. The converse direction is `Matrix.toLin_kronecker`. The rules `Matrix.det_kronecker` and `Matrix.trace_kronecker` are in `Mathlib.LinearAlgebra.Matrix.Kronecker`.

<?decl TensorProduct.toMatrix_map?>
:::

**Theorem (Hom as a tensor product).** If $M$ is free of finite rank, then $\Theta : M^* \otimes N \to \operatorname{Hom}(M, N)$ is an isomorphism.

*Proof.* Let $(e_i)$ be a basis of $M$ and $(e_i^*)$ the dual basis (Volume 7, Chapter 6). Define $\Psi(h) = \sum_i e_i^* \otimes h(e_i)$, which is linear in $h$. First, $\Theta(\Psi(h))(e_j) = \sum_i e_i^*(e_j) \, h(e_i) = h(e_j)$, so $\Theta \circ \Psi = \mathrm{id}$. Next, for a pure tensor, $\Psi(\Theta(\varphi \otimes n)) = \sum_i e_i^* \otimes \varphi(e_i) n = \big(\sum_i \varphi(e_i) e_i^*\big) \otimes n = \varphi \otimes n$, because $\varphi = \sum_i \varphi(e_i) e_i^*$. Pure tensors generate, so $\Psi \circ \Theta = \mathrm{id}$. $\square$

Under $\Theta$ a pure tensor $\varphi \otimes n$ is a map of rank at most $1$, and the identity of $K^n$ is $\sum_i e_i^* \otimes e_i$.

**Theorem (Trace and contraction).** If $M$ is free of finite rank, then $\operatorname{tr}(\Theta(t)) = c(t)$ for each $t \in M^* \otimes M$.

*Proof.* Both sides are linear in $t$, so it suffices to check pure tensors. Write $m = \sum_i m_i e_i$. The map $\Theta(\varphi \otimes m)$ sends $e_j$ to $\varphi(e_j) m$, so its matrix has the entry $m_i \varphi(e_j)$ at $(i, j)$. Its trace is $\sum_i m_i \varphi(e_i) = \varphi(\sum_i m_i e_i) = \varphi(m) = c(\varphi \otimes m)$. $\square$

The contraction does not use a basis. So this theorem gives a definition of the trace that does not depend on a basis.

::: mathlib
`dualTensorHomEquiv` · `Mathlib.LinearAlgebra.Contraction`

The equivalence `Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N` for a finite projective module `M`, a more general hypothesis than finite free. The version with an explicit basis is `dualTensorHomEquivOfBasis`. The theorem on the trace is `LinearMap.trace_eq_contract`, in `Mathlib.LinearAlgebra.Trace`.

<?decl dualTensorHomEquiv?>
<?decl LinearMap.trace_eq_contract?>
:::

::: mathlib
`coevaluation` · `Mathlib.LinearAlgebra.Coevaluation`

For a finite dimensional vector space `V` over a field `K`, the linear map `coevaluation K V : K →ₗ[K] V ⊗[K] Module.Dual K V` with `coevaluation_apply_one`: the image of $1$ is $\sum_i e_i \otimes e_i^*$, the identity under $\Theta$ after a swap.

<?decl coevaluation?>
:::

### Examples

**Example ($\mathbb{R}^2 \otimes \mathbb{R}^3$).** The space $\mathbb{R}^2 \otimes \mathbb{R}^3$ has dimension $6$, with the basis $e_i \otimes f_j$ for $i \le 2$, $j \le 3$, and $\Phi$ identifies it with the $2 \times 3$ matrices. The tensor $(1, 2) \otimes (1, 2, 3)$ gives the matrix $\begin{pmatrix} 1 & 2 & 3 \\ 2 & 4 & 6 \end{pmatrix}$ of rank $1$. The tensor $t = e_1 \otimes f_1 + e_2 \otimes f_2$ gives $\begin{pmatrix} 1 & 0 & 0 \\ 0 & 1 & 0 \end{pmatrix}$, of rank $2$. So $t$ has rank $2$ and is not a pure tensor.

**Example (A Kronecker product).** Let $A = \begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix}$ and $B = \operatorname{diag}(1, 2, 3)$. In the order $(1,1), (1,2), (1,3), (2,1), (2,2), (2,3)$ of the pairs,
$$A \otimes B = \begin{pmatrix} B & 2 B \\ 0 & B \end{pmatrix},$$
a $6 \times 6$ matrix. It is block upper triangular, so $\det(A \otimes B) = (\det B)^2 = 36$ and $\operatorname{tr}(A \otimes B) = 2 \operatorname{tr} B = 12$. The general formulas agree: $\det A^3 \det B^2 = 1 \cdot 36$ and $\operatorname{tr} A \operatorname{tr} B = 2 \cdot 6$.

**Counterexample (Finite rank is needed).** Let $V$ be a vector space with a countably infinite basis $(e_k)_{k \ge 0}$. For $t = \sum_{k=1}^{r} \varphi_k \otimes v_k$, the image of $\Theta(t)$ lies in the span of $v_1, \dots, v_r$. So each map in the image of $\Theta$ has finite rank, and the identity of $V$ is not in the image. So the theorem needs $M$ of finite rank.

### The library around it

The lemma `TensorProduct.exists_finset` writes each element as a finite sum of pure tensors. The index of this edition has no declaration for the rank of a tensor.

### Exercises

1. (A) Write the $4 \times 4$ Kronecker product of $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ with itself. Hint: the block form $(A_{i j} B)$.
2. (A) Find the rank of $e_1 \otimes f_1 + 2 e_1 \otimes f_3 + e_2 \otimes f_2 + 2 e_2 \otimes f_3$ in $\mathbb{Q}^2 \otimes \mathbb{Q}^3$. Hint: write the matrix.
3. (A) Show that the swap $M \otimes N \cong N \otimes M$ of Section 1 turns $\Phi(t)$ into its transpose. Hint: check $x \otimes y$.
4. (B) Show that $\operatorname{rank}(A \otimes B) = \operatorname{rank} A \cdot \operatorname{rank} B$ over a field. Hint: normal forms of $A$ and $B$.
5. (B) Show that $(A \otimes B)(A' \otimes B') = A A' \otimes B B'$. Hint: functoriality of $f \otimes g$ and the theorem on the Kronecker product.
6. (B) Prove $\det(A \otimes B) = \det A^n \det B^m$ for $A$ of size $m$ and $B$ of size $n$. Hint: $A \otimes B = (A \otimes I_n)(I_m \otimes B)$.
7. (C) Over a field, show that the elements of rank at most $1$ in $K^m \otimes K^n$ are the zeros of the $2 \times 2$ minors of $\Phi(t)$, and that they do not form a subspace for $m, n \ge 2$. Hint: $e_1 \otimes f_1$ and $e_2 \otimes f_2$.

### Notes and history

The rank of a tensor in a product of three or more spaces is not the rank of a matrix, and it is hard to compute. That case belongs to Chapter 3.

### Reference

<?reference?>
