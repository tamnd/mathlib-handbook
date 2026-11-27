---
title: Annihilators, the dual map and the transpose
kind: theory
modules:
  - Mathlib.LinearAlgebra.Dual.Lemmas
  - Mathlib.LinearAlgebra.Matrix.Dual
explains:
  E3: [Submodule.dualAnnihilator, LinearMap.dualMap, Subspace.finrank_add_finrank_dualAnnihilator_eq]
  E2: [Submodule.mem_dualAnnihilator, Subspace.dual_finrank_eq, LinearMap.dualMap_apply, LinearMap.toMatrix_transpose, LinearMap.ker_dualMap_eq_dualAnnihilator_range, LinearMap.range_dualMap_eq_dualAnnihilator_ker, LinearMap.finrank_range_dualMap_eq_finrank_range, LinearMap.dualMap_injective_iff, Submodule.dualCoannihilator, Subspace.quotAnnihilatorEquiv, Module.Dual.transpose]
  E1: auto
families: []
requires: [V07.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Annihilators, the dual map and the transpose

### Overview

A subspace $W$ of $V$ is cut out by the functionals that vanish on it, and these functionals form the annihilator $W^0 \subseteq V^*$. A linear map $f : V \to W$ gives the dual map $f^* : W^* \to V^*$, $\varphi \mapsto \varphi \circ f$. This section proves $\dim W + \dim W^0 = \dim V$, shows that the matrix of $f^*$ in the dual bases is the transpose of the matrix of $f$, and computes the kernel and the range of $f^*$. These results give a second proof that the row rank equals the column rank. The section ends with a pointer to the inner product spaces, which Mathlib places in the analysis volumes.

### Definitions

**Definition (Annihilator).** For a submodule $W \subseteq M$, the annihilator is $W^0 = \{\varphi \in M^* : \varphi(w) = 0 \text{ for all } w \in W\}$, a submodule of $M^*$. For a submodule $U \subseteq M^*$, the coannihilator is $\{x \in M : \varphi(x) = 0 \text{ for all } \varphi \in U\}$.

::: mathlib
`Submodule.dualAnnihilator` · `Mathlib.LinearAlgebra.Dual.Defs`

The annihilator `W.dualAnnihilator : Submodule R (Dual R M)`. The name avoids a clash with `Submodule.annihilator`, the ideal of the scalars that kill a module.

<?decl Submodule.dualAnnihilator?>
:::

::: mathlib
`Submodule.mem_dualAnnihilator` · `Mathlib.LinearAlgebra.Dual.Defs`

The criterion `φ ∈ W.dualAnnihilator ↔ ∀ w ∈ W, φ w = 0`.

<?decl Submodule.mem_dualAnnihilator?>
:::

::: mathlib
`Submodule.dualCoannihilator` · `Mathlib.LinearAlgebra.Dual.Defs`

The coannihilator `U.dualCoannihilator : Submodule R M` of a submodule `U` of the dual. Over a field in finite dimension, the two operations are inverse bijections between the subspaces of `V` and of `V*`.

<?decl Submodule.dualCoannihilator?>
:::

**Definition (Dual map).** For a linear map $f : M \to N$, the dual map $f^* : N^* \to M^*$ is $f^*(\varphi) = \varphi \circ f$.

The dual map reverses the order of composition: $(g \circ f)^* = f^* \circ g^*$, and $\mathrm{id}^* = \mathrm{id}$.

::: mathlib
`LinearMap.dualMap` · `Mathlib.LinearAlgebra.Dual.Defs`

The dual map `f.dualMap : Dual R N →ₗ[R] Dual R M`.

<?decl LinearMap.dualMap?>
:::

::: mathlib
`LinearMap.dualMap_apply` · `Mathlib.LinearAlgebra.Dual.Defs`

The formula `f.dualMap g x = g (f x)`.

<?decl LinearMap.dualMap_apply?>
:::

::: mathlib
`Module.Dual.transpose` · `Mathlib.LinearAlgebra.Dual.Defs`

The dual map as a linear map in `f`: `Dual.transpose : (M →ₗ[R] M') →ₗ[R] Dual R M' →ₗ[R] Dual R M`. It is the form that the matrix statement below uses.

<?decl Module.Dual.transpose?>
:::

### Theorems and proofs

**Theorem (Dimension of the annihilator).** For a subspace $W$ of a space $V$ of finite dimension $n$, $\dim W + \dim W^0 = n$.

*Proof.* Let $w_1, \dots, w_k$ be a basis of $W$, and extend it to a basis $w_1, \dots, w_n$ of $V$, by Chapter 2. Let $w_1^*, \dots, w_n^*$ be the dual basis. A functional $\varphi = \sum_i \varphi(w_i) w_i^*$ lies in $W^0$ if and only if $\varphi(w_i) = 0$ for $i \le k$, that is, if and only if $\varphi$ lies in the span of $w_{k+1}^*, \dots, w_n^*$. These $n - k$ functionals are independent, so $\dim W^0 = n - k$. $\square$

::: mathlib
`Subspace.finrank_add_finrank_dualAnnihilator_eq` · `Mathlib.LinearAlgebra.Dual.Lemmas`

The statement `finrank K W + finrank K W.dualAnnihilator = finrank K V`.

<?decl Subspace.finrank_add_finrank_dualAnnihilator_eq?>
:::

::: mathlib
`Subspace.dual_finrank_eq` · `Mathlib.LinearAlgebra.Dual.Lemmas`

The statement `finrank K (Dual K V) = finrank K V`. Since `finrank` is `0` in infinite dimension, it needs no hypothesis of finiteness.

<?decl Subspace.dual_finrank_eq?>
:::

::: mathlib
`Subspace.quotAnnihilatorEquiv` · `Mathlib.LinearAlgebra.Dual.Lemmas`

The isomorphism `(Dual K V ⧸ W.dualAnnihilator) ≃ₗ[K] Dual K W`, from the restriction of functionals to `W`. It gives the formula of the theorem in each dimension.

<?decl Subspace.quotAnnihilatorEquiv?>
:::

**Theorem (Matrix of the dual map).** Let $f : V \to W$ have the matrix $A$ in the bases $b$ of $V$ and $c$ of $W$. Then $f^*$ has the matrix $A^{\mathsf{T}}$ in the dual bases $c^*$ of $W^*$ and $b^*$ of $V^*$.

*Proof.* By definition of the matrix, $f(b_j) = \sum_i A_{ij} c_i$. The functional $f^*(c_i^*) = c_i^* \circ f$ takes the value $c_i^*(f(b_j)) = A_{ij}$ at $b_j$. By the expansion in the dual basis, $f^*(c_i^*) = \sum_j A_{ij} b_j^*$. So the column $i$ of the matrix of $f^*$ is the row $i$ of $A$. $\square$

::: mathlib
`LinearMap.toMatrix_transpose` · `Mathlib.LinearAlgebra.Matrix.Dual`

The statement `toMatrix B₂.dualBasis B₁.dualBasis (Dual.transpose u) = (toMatrix B₁ B₂ u)ᵀ`.

<?decl LinearMap.toMatrix_transpose?>
:::

**Theorem (Kernel and range of the dual map).** For $f : V \to W$ linear:

1. $\ker f^* = (\operatorname{im} f)^0$;
2. if $V$ and $W$ have finite dimension, $\operatorname{im} f^* = (\ker f)^0$, and $\operatorname{rank} f^* = \operatorname{rank} f$;
3. $f^*$ is injective if and only if $f$ is surjective.

*Proof.* Part 1: $f^* \varphi = \varphi \circ f = 0$ if and only if $\varphi$ vanishes on $\operatorname{im} f$. Part 3 follows from part 1 in finite dimension, since $(\operatorname{im} f)^0 = 0$ if and only if $\operatorname{im} f = W$, by the dimension of the annihilator. Part 2: if $\varphi = \psi \circ f$, then $\varphi$ vanishes on $\ker f$, so $\operatorname{im} f^* \subseteq (\ker f)^0$. Let $n = \dim V$, $m = \dim W$ and $r = \operatorname{rank} f$. By part 1, the dimension of the annihilator and rank-nullity,
$$\dim \operatorname{im} f^* = m - \dim (\operatorname{im} f)^0 = m - (m - r) = r, \qquad \dim (\ker f)^0 = n - (n - r) = r.$$
So the inclusion is an equality, and $\operatorname{rank} f^* = r$. $\square$

**Corollary (Row rank equals column rank).** For each matrix $A$ over a field, $\operatorname{rank} A^{\mathsf{T}} = \operatorname{rank} A$.

*Proof.* $A^{\mathsf{T}}$ is the matrix of the dual map of $x \mapsto A x$ in the dual bases, and the dual map has the same rank. $\square$

This is the proof that Mathlib uses for `Matrix.rank_transpose` in Chapter 3.

::: mathlib
`LinearMap.ker_dualMap_eq_dualAnnihilator_range` · `Mathlib.LinearAlgebra.Dual.Defs`

Part 1: `f.dualMap.ker = f.range.dualAnnihilator`, over each commutative semiring.

<?decl LinearMap.ker_dualMap_eq_dualAnnihilator_range?>
:::

::: mathlib
`LinearMap.range_dualMap_eq_dualAnnihilator_ker` · `Mathlib.LinearAlgebra.Dual.Lemmas`

Part 2: `f.dualMap.range = f.ker.dualAnnihilator`, over a field. Mathlib proves it in each dimension, with the extension of functionals from a subspace.

<?decl LinearMap.range_dualMap_eq_dualAnnihilator_ker?>
:::

::: mathlib
`LinearMap.finrank_range_dualMap_eq_finrank_range` · `Mathlib.LinearAlgebra.Dual.Lemmas`

The equality of the ranks: `finrank K f.dualMap.range = finrank K f.range`.

<?decl LinearMap.finrank_range_dualMap_eq_finrank_range?>
:::

::: mathlib
`LinearMap.dualMap_injective_iff` · `Mathlib.LinearAlgebra.Dual.Lemmas`

Part 3: `Injective f.dualMap ↔ Surjective f`, over a field.

<?decl LinearMap.dualMap_injective_iff?>
:::

### Examples

**Example (An annihilator in $\mathbb{Q}^3$).** Let $W$ be the line spanned by $(1, 1, 1)$. Write a functional as a row vector $(a, b, c)$. It lies in $W^0$ if and only if $a + b + c = 0$. So $W^0$ has the basis $(1, -1, 0)$ and $(0, 1, -1)$, and $\dim W + \dim W^0 = 1 + 2 = 3$. The coannihilator of $W^0$ is the set of the $x$ with $x_1 - x_2 = 0$ and $x_2 - x_3 = 0$, which is $W$ again.

**Example (The row space as an annihilator).** Let $A = \begin{pmatrix} 1 & 2 & 3 \\ 4 & 5 & 6 \\ 7 & 8 & 9 \end{pmatrix}$, as in Chapter 3, with the kernel spanned by $(1, -2, 1)$. The range of the dual map is spanned by the rows of $A$, read as functionals. By part 2 it is $(\ker A)^0$, the set of the row vectors $\varphi$ with $\varphi_1 - 2\varphi_2 + \varphi_3 = 0$. Check: $1 - 4 + 3 = 0$, $4 - 10 + 6 = 0$, $7 - 16 + 9 = 0$. The plane has dimension $2$, the rank of $A$.

**Example (The dual of the derivative).** Let $V$ be the polynomials of degree at most $2$ over $\mathbb{Q}$, with the basis $1, X, X^2$, and $D = d/dX$. The matrix of $D$ is $\begin{pmatrix} 0 & 1 & 0 \\ 0 & 0 & 2 \\ 0 & 0 & 0 \end{pmatrix}$. The dual map sends the coordinate functional $(X^2)^*$ to $(X^2)^* \circ D$, which is $0$ since $D p$ has degree at most $1$. It sends $X^*$ to $p \mapsto$ the coefficient of $X$ in $p'$, which is $2 (X^2)^*$. These are the columns of the transpose matrix $\begin{pmatrix} 0 & 0 & 0 \\ 1 & 0 & 0 \\ 0 & 2 & 0 \end{pmatrix}$. The kernel of $D^*$ is spanned by $(X^2)^*$, the annihilator of $\operatorname{im} D$, which is the space of the polynomials of degree at most $1$.

**Counterexample (Infinite dimension).** On the space $V = \mathbb{Q}[X]$, the map $f$ of the multiplication by $X$ is injective and not surjective. Its dual map sends $\varphi$ to $p \mapsto \varphi(X p)$. In the identification $V^* \cong \mathbb{Q}^{\mathbb{N}}$, it is the shift $(a_0, a_1, \dots) \mapsto (a_1, a_2, \dots)$, which is surjective and not injective. The kernel is the line of the sequences $(a_0, 0, 0, \dots)$, the annihilator of $X \mathbb{Q}[X]$.

### The library around it

The results over a field are in `Mathlib.LinearAlgebra.Dual.Lemmas`, and the statements on matrices are in `Mathlib.LinearAlgebra.Matrix.Dual`. The bilinear forms and their nondegeneracy, which give maps $V \to V^*$ without a basis, are under `Mathlib.LinearAlgebra.BilinearForm` and `Mathlib.LinearAlgebra.SesquilinearForm`.

Inner products are not part of this volume. Mathlib places the inner product spaces over $\mathbb{R}$ and $\mathbb{C}$ in the analysis library, under `Mathlib.Analysis.InnerProductSpace`, since an inner product gives a norm and a topology. The handbook treats them in Volume 16. The boxes below name the main entries for orientation.

::: mathlib
`InnerProductSpace` · `Mathlib.Analysis.InnerProductSpace.Defs`

The class of the inner product spaces over `𝕜`, which is `ℝ` or `ℂ` through the class `RCLike`. It extends a normed space.

<?decl InnerProductSpace?>
:::

::: mathlib
`InnerProductSpace.toDual` · `Mathlib.Analysis.InnerProductSpace.Dual`

The theorem of Riesz as an isometric equivalence between a complete inner product space and its continuous dual. It is the analytic form of the isomorphism $V \cong V^*$ given by a nondegenerate form.

<?decl InnerProductSpace.toDual?>
:::

::: mathlib
`OrthonormalBasis` · `Mathlib.Analysis.InnerProductSpace.PiL2`

The orthonormal bases of a space of finite dimension, as a structure with its own coercion to a family of vectors.

<?decl OrthonormalBasis?>
:::

::: mathlib
`InnerProductSpace.gramSchmidt` · `Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`

The process of Gram and Schmidt, which turns a family of vectors into an orthogonal family with the same partial spans.

<?decl InnerProductSpace.gramSchmidt?>
:::

::: mathlib
`LinearMap.IsSymmetric.eigenvectorBasis` · `Mathlib.Analysis.InnerProductSpace.Spectrum`

The spectral theorem: a symmetric operator on a space of finite dimension has an orthonormal basis of eigenvectors. It is the result of the eigenvalue theory of Chapter 5 for the symmetric matrices.

<?decl LinearMap.IsSymmetric.eigenvectorBasis?>
:::

### Exercises

1. (A) Find a basis of the annihilator of the plane $x + 2y - z = 0$ in $\mathbb{Q}^3$.
2. (A) Show that $W_1 \subseteq W_2$ implies $W_2^0 \subseteq W_1^0$.
3. (A) Show that $(g \circ f)^* = f^* \circ g^*$, and deduce $(A B)^{\mathsf{T}} = B^{\mathsf{T}} A^{\mathsf{T}}$ from the matrix of the dual map.
4. (B) Show that $(W_1 + W_2)^0 = W_1^0 \cap W_2^0$ and, in finite dimension, $(W_1 \cap W_2)^0 = W_1^0 + W_2^0$. Hint: for the second, compare the dimensions.
5. (B) Show that each subspace of dimension $k$ of $K^n$ is the set of the solutions of $n - k$ independent linear equations.
6. (C) Let $f : V \to V$ in finite dimension. Show that a subspace $U$ is invariant under $f$ if and only if $U^0$ is invariant under $f^*$. Deduce that $f$ and $f^*$ have the same characteristic polynomial.

### Notes and history

The transpose of a matrix appears in the work of Cayley in 1858. The interpretation of the transpose as the dual map, and the formula $\operatorname{im} f^* = (\ker f)^0$, became standard with the abstract treatment of linear algebra by Bourbaki and in the texts of the mid twentieth century. In functional analysis, the corresponding statements for the adjoint of an operator are the closed range theorem of Banach.

In Mathlib, the annihilators and the dual map are in the files on the dual space by Johan Commelin, Fabian Glöckle and Kyle Miller. The proof of `Matrix.rank_transpose` through `LinearMap.finrank_range_dualMap_eq_finrank_range` shows how Mathlib reuses an abstract result for a matrix statement.

### Reference

<?reference?>
