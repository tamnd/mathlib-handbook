---
title: Orthogonality
kind: theory
modules:
  - Mathlib.LinearAlgebra.BilinearForm.Orthogonal
  - Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
explains:
  E3: [LinearMap.BilinForm.orthogonal, LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate, LinearMap.BilinForm.finrank_add_finrank_orthogonal]
  E2: [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.iIsOrtho, LinearMap.BilinForm.linearIndependent_of_iIsOrtho, LinearMap.BilinForm.isCompl_span_singleton_orthogonal, LinearMap.BilinForm.orthogonal_orthogonal, LinearMap.BilinForm.finrank_orthogonal, LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal, LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self, LinearMap.BilinForm.le_orthogonal_orthogonal, LinearMap.BilinForm.orthogonal_top_eq_ker, LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot, Submodule.orthogonalBilin]
  E1: auto
families: []
requires: [V08.C01, V07.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Orthogonality

### Overview

A bilinear form gives a notion of perpendicular vectors: $x$ and $y$ are orthogonal when $B(x, y) = 0$. Unlike the Euclidean case, a nonzero vector can be orthogonal to itself.

It proves the dimension formula for $W^{\perp}$, the criterion $V = W \oplus W^{\perp}$, the existence of an orthogonal basis for a symmetric form when $2$ is invertible, and the normal form of an alternating form.

Section 1 and the dual space of Volume 7, Chapter 6 are used throughout.

### Definitions

Let $R$ be a commutative ring, $M$ an $R$-module and $B$ a bilinear form on $M$.

**Definition (Orthogonal).** Two vectors $x, y$ are orthogonal if $B(x, y) = 0$. For a submodule $N$, the orthogonal of $N$ is
$$N^{\perp} = \{ m \in M : B(n, m) = 0 \text{ for all } n \in N \}.$$
A vector $x \neq 0$ is isotropic if $B(x, x) = 0$.

For a reflexive form the side does not matter; the orthogonal $M^{\perp}$ is the right kernel of $B$.

::: mathlib
`LinearMap.BilinForm.orthogonal` · `Mathlib.LinearAlgebra.BilinearForm.Orthogonal`

`B.orthogonal N` is `{m | ∀ n ∈ N, B n m = 0}`, with the vectors of `N` on the left; membership unfolds with `mem_orthogonal_iff`.

<?decl LinearMap.BilinForm.orthogonal?>
:::

<?decl LinearMap.BilinForm.mem_orthogonal_iff?>

<?decl LinearMap.BilinForm.orthogonal_top_eq_ker?>

<?decl Submodule.orthogonalBilin?>

**Definition (Orthogonal family).** A family $(v_i)_{i \in I}$ in $M$ is orthogonal if $B(v_i, v_j) = 0$ for all $i \neq j$. An orthogonal basis is a basis that is an orthogonal family.

::: mathlib
`LinearMap.BilinForm.iIsOrtho` · `Mathlib.LinearAlgebra.BilinearForm.Orthogonal`

`B.iIsOrtho v` states `B (v i) (v j) = 0` for `i ≠ j`; the sesquilinear version is `LinearMap.IsOrthoᵢ`.

<?decl LinearMap.BilinForm.iIsOrtho?>
:::

### Theorems and proofs

From here on $V$ is a vector space of finite dimension $n$ over a field $K$.

**Proposition (Orthogonal families).** Let $(v_i)$ be an orthogonal family with $B(v_i, v_i) \neq 0$ for all $i$. Then the family is linearly independent. If it is a basis, then $B$ is nondegenerate if and only if $B(v_i, v_i) \neq 0$ for all $i$.

*Proof.* Let $\sum_i a_i v_i = 0$ be a finite relation. Apply $B(v_j, -)$: orthogonality leaves $a_j B(v_j, v_j) = 0$, so $a_j = 0$. For the second claim, the matrix in the basis is diagonal with the entries $B(v_i, v_i)$, and by Section 1 the form is nondegenerate if and only if this determinant $\prod_i B(v_i, v_i)$ is not zero. $\square$

<?decl LinearMap.BilinForm.linearIndependent_of_iIsOrtho?>

<?decl LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self?>

**Theorem (Dimension formula).** Let $B$ be reflexive and let $W$ be a subspace of $V$. Then
$$\dim W + \dim W^{\perp} = \dim V + \dim(W \cap V^{\perp}).$$

*Proof.* Let $w_1, \dots, w_k$ be a basis of $W$. A vector $v$ is in $W^{\perp}$ if and only if $B(w_i, v) = 0$ for $i = 1, \dots, k$. So $W^{\perp}$ is the kernel of the linear map $\varphi : V \to K^k$, $v \mapsto (B(w_i, v))_i$, and $\dim W^{\perp} = n - \operatorname{rank} \varphi$ by rank-nullity. The rank of $\varphi$ is the dimension of the span of the linear forms $B(w_i, -)$ in $V^*$, because the rank of a matrix equals the rank of its rows (Volume 7, Chapter 6). This span is the image of the linear map $\psi : W \to V^*$, $w \mapsto B(w, -)$. The kernel of $\psi$ is the set of $w \in W$ with $B(w, v) = 0$ for all $v$. Since $B$ is reflexive, this is $W \cap V^{\perp}$. So $\operatorname{rank} \varphi = k - \dim(W \cap V^{\perp})$ and
$$\dim W^{\perp} = n - k + \dim(W \cap V^{\perp}). \qquad \square$$

::: mathlib
`LinearMap.BilinForm.finrank_add_finrank_orthogonal` · `Mathlib.LinearAlgebra.BilinearForm.Orthogonal`

The formula for `B.IsRefl`, with `W ⊓ B.orthogonal ⊤` as the correction term. For a nondegenerate form, `finrank_orthogonal` gives `finrank V - finrank W`.

<?decl LinearMap.BilinForm.finrank_add_finrank_orthogonal?>
:::

<?decl LinearMap.BilinForm.finrank_orthogonal?>

**Corollary (Double orthogonal).** If $B$ is reflexive, then $W \subseteq (W^{\perp})^{\perp}$. If $B$ is also nondegenerate, then $(W^{\perp})^{\perp} = W$.

*Proof.* For $w \in W$ and $m \in W^{\perp}$, $B(w, m) = 0$, so $B(m, w) = 0$ by reflexivity, and $w \in (W^{\perp})^{\perp}$. If $B$ is nondegenerate, then $V^{\perp} = 0$, and the dimension formula gives $\dim W^{\perp} = n - \dim W$ and $\dim (W^{\perp})^{\perp} = n - \dim W^{\perp} = \dim W$. A subspace of $(W^{\perp})^{\perp}$ of the same dimension is equal to it. $\square$

<?decl LinearMap.BilinForm.le_orthogonal_orthogonal?>

<?decl LinearMap.BilinForm.orthogonal_orthogonal?>

**Theorem (Orthogonal complement).** Let $B$ be reflexive and let $W$ be a subspace of $V$. Then $V = W \oplus W^{\perp}$ if and only if $B|_W$ is nondegenerate.

*Proof.* The right kernel of $B|_W$ is the set of $m \in W$ with $B(w, m) = 0$ for all $w \in W$, that is $W \cap W^{\perp}$. Since $B$ is reflexive, the left kernel of $B|_W$ is the same set. So $B|_W$ is nondegenerate if and only if $W \cap W^{\perp} = 0$. If $V = W \oplus W^{\perp}$, then $W \cap W^{\perp} = 0$. Conversely, suppose $W \cap W^{\perp} = 0$. Since $V^{\perp} \subseteq W^{\perp}$, also $W \cap V^{\perp} = 0$, and the dimension formula gives $\dim W + \dim W^{\perp} = \dim V$. Two subspaces with zero intersection and complementary dimensions are complements. $\square$

::: mathlib
`LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate` · `Mathlib.LinearAlgebra.BilinearForm.Orthogonal`

The direction from a nondegenerate restriction to `IsCompl W (B.orthogonal W)`; the equivalence is `restrict_nondegenerate_iff_isCompl_orthogonal`.

<?decl LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate?>
:::

<?decl LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal?>

**Lemma (Anisotropic line).** If $B(x, x) \neq 0$, then $V = K x \oplus (K x)^{\perp}$. This holds for each form, reflexive or not.

*Proof.* If $a x \in (K x)^{\perp}$, then $a B(x, x) = 0$, so $a = 0$. For $v \in V$, put $c = B(x, v) / B(x, x)$. Then $B(x, v - c x) = 0$, so $v = c x + (v - c x)$ with $v - c x \in (K x)^{\perp}$. $\square$

<?decl LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot?>

<?decl LinearMap.BilinForm.isCompl_span_singleton_orthogonal?>

**Theorem (Orthogonal basis).** Suppose $2 \neq 0$ in $K$. Each symmetric form $B$ on $V$ has an orthogonal basis, in which its matrix is diagonal.

*Proof.* Induction on $n$. For $n = 0$ the empty basis works. Let $n \ge 1$. If $B = 0$, each basis is orthogonal. If $B \neq 0$, there is an $x$ with $B(x, x) \neq 0$: otherwise the polarization identity of Section 1 gives $2 B(x, y) = B(x + y, x + y) - B(x, x) - B(y, y) = 0$ for all $x, y$, and $B = 0$ since $2$ is invertible. By the lemma, $V = K x \oplus U$ with $U = (K x)^{\perp}$ of dimension $n - 1$. The restriction $B|_U$ is symmetric, so by induction $U$ has an orthogonal basis $u_2, \dots, u_n$. Then $x, u_2, \dots, u_n$ is a basis of $V$. It is orthogonal, since $B(x, u_i) = 0$ by the choice of $U$ and $B(u_i, x) = B(x, u_i)$ by symmetry. $\square$

::: mathlib
`LinearMap.BilinForm.exists_orthogonal_basis` · `Mathlib.LinearAlgebra.QuadraticForm.Basic`

For symmetric `B` over a field with `Invertible (2 : K)`, a basis `v` with `LinearMap.IsOrthoᵢ B v`. It lives with the quadratic forms.

<?decl LinearMap.BilinForm.exists_orthogonal_basis?>
:::

<?decl LinearMap.BilinForm.exists_bilinForm_self_ne_zero?>

**Theorem (Alternating forms).** Let $B$ be a nondegenerate alternating form on $V$. Then $n = 2m$ is even, and $V$ has a basis $e_1, f_1, \dots, e_m, f_m$ with $B(e_i, f_i) = 1$, $B(f_i, e_i) = -1$, and $B = 0$ on all other pairs of basis vectors.

*Proof.* Induction on $n$. For $n = 0$ there is nothing to prove. Let $n \ge 1$ and pick $e_1 \neq 0$. Since $B$ is nondegenerate, there is a $y$ with $B(e_1, y) \neq 0$; put $f_1 = y / B(e_1, y)$, so $B(e_1, f_1) = 1$ and $B(f_1, e_1) = -1$ by Section 1. The vectors $e_1, f_1$ are independent: if $f_1 = c e_1$, then $B(e_1, f_1) = c B(e_1, e_1) = 0$. Let $H = K e_1 + K f_1$. The matrix of $B|_H$ is $\begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$ with determinant $1$, so $B|_H$ is nondegenerate. An alternating form is reflexive, so $V = H \oplus H^{\perp}$ by the complement theorem. The restriction to $H^{\perp}$ is alternating and nondegenerate: if $u \in H^{\perp}$ is orthogonal to $H^{\perp}$, then $u$ is orthogonal to $H$ by reflexivity, so to all of $V$, and $u = 0$. By induction $\dim H^{\perp} = 2(m - 1)$ with a basis $e_2, f_2, \dots, e_m, f_m$ of the given form. Together with $e_1, f_1$ this is the basis. $\square$

The index of this edition has no declaration for this normal form.

### Examples

**Example (The hyperbolic plane).** On $\mathbb{Q}^2$ let $B(x, y) = x_1 y_2 + x_2 y_1$, with matrix $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. It is nondegenerate, but $W = \mathbb{Q} e_1$ has $W^{\perp} = W$ and $B|_W = 0$. The vectors $v_1 = (1, 1)$ and $v_2 = (1, -1)$ have $B(v_1, v_1) = 2$, $B(v_2, v_2) = -2$ and $B(v_1, v_2) = -1 + 1 = 0$, so in this basis the matrix is $\operatorname{diag}(2, -2)$.

**Counterexample (No orthogonal basis in characteristic 2).** Over $\mathbb{F}_2$ the same formula $B(x, y) = x_1 y_2 + x_2 y_1$ gives $B(x, x) = 2 x_1 x_2 = 0$, so $B$ is alternating and nonzero. In an orthogonal basis the matrix would be diagonal with diagonal entries $B(v_i, v_i) = 0$, so $B$ would be $0$. So $B$ has no orthogonal basis, and the hypothesis $2 \neq 0$ of the theorem is necessary.

**Example (A diagonalization in dimension 3).** On $\mathbb{Q}^3$ let $B$ have the matrix
$$A = \begin{pmatrix} 0 & 1 & 1 \\ 1 & 0 & 1 \\ 1 & 1 & 0 \end{pmatrix}, \qquad B(x, y) = x_1 y_2 + x_2 y_1 + x_1 y_3 + x_3 y_1 + x_2 y_3 + x_3 y_2.$$
The diagonal is zero, so the proof starts with $v_1 = e_1 + e_2$, with $B(v_1, v_1) = 2$ and $v_1^{\perp} = \{y_1 + y_2 + 2 y_3 = 0\}$. This plane contains $v_2 = e_1 - e_2$, with $B(v_2, v_2) = -2$ and $B(v_2, y) = y_2 - y_1$. A vector orthogonal to both is $v_3 = (1, 1, -1)$, and $A v_3 = (0, 0, 2)$ gives $B(v_3, v_3) = -2$. So the matrix in the basis $v_1, v_2, v_3$ is $\operatorname{diag}(2, -2, -2)$. As a check, $\det A = 2$ and $\det P = 2$ for the matrix $P$ of columns $v_i$, and $(\det P)^2 \det A = 8 = 2 \cdot (-2) \cdot (-2)$.

### The library around it

The sesquilinear versions are in `Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal`. Chapter 6 continues the diagonalization; in the inner product spaces of Volume 16, $W^{\perp}$ is always a complement.

### Exercises

1. (A) Show that $W_1 \subseteq W_2$ implies $W_2^{\perp} \subseteq W_1^{\perp}$, and that $(W_1 + W_2)^{\perp} = W_1^{\perp} \cap W_2^{\perp}$.
2. (A) Find an orthogonal basis of $\mathbb{Q}^2$ for the form with matrix $\begin{pmatrix} 1 & 2 \\ 2 & 1 \end{pmatrix}$, and the diagonal matrix it gives. Hint: start with $e_1$.
3. (B) Let $B$ be nondegenerate and reflexive, and let $W$ be totally isotropic, that is $W \subseteq W^{\perp}$. Show $\dim W \le \dim V / 2$. Hint: the dimension formula.
4. (B) Let $B$ be symmetric with $2 \neq 0$, and let $x_1, \dots, x_r$ be orthogonal with $B(x_i, x_i) \neq 0$. Show that they extend to an orthogonal basis. Hint: the orthogonal of their span.
5. (C) Extend the theorem on alternating forms to degenerate alternating forms: show that there is a basis $e_1, f_1, \dots, e_m, f_m, g_1, \dots, g_r$ with the $g_j$ a basis of $V^{\perp}$. Hint: the restriction to a complement of $V^{\perp}$ is nondegenerate.
6. (C) Let $B$ be symmetric and nondegenerate with $2 \neq 0$ in $K$. Show that $B|_W$ is nondegenerate if and only if $B|_{W^{\perp}}$ is nondegenerate. Hint: the complement theorem and the double orthogonal.

### Notes and history

The orthogonal basis theorem for symmetric forms is the matrix form of the reduction of a quadratic form to a sum of squares, often credited to Lagrange.

### Reference

<?reference?>
