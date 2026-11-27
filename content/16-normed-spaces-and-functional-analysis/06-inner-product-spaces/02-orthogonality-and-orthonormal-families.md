---
title: Orthogonality and orthonormal families
kind: theory
modules:
  - Mathlib.Analysis.InnerProductSpace.Orthonormal
  - Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
  - Mathlib.Analysis.InnerProductSpace.PiL2
  - Mathlib.Analysis.InnerProductSpace.Orthogonal
explains:
  E3: [Orthonormal, Orthonormal.sum_inner_products_le, InnerProductSpace.gramSchmidt, OrthonormalBasis]
  E2: [orthonormal_iff_ite, Orthonormal.linearIndependent, Orthonormal.norm_eq_one, Orthonormal.inner_eq_zero, Orthonormal.tsum_inner_products_le, norm_add_sq_eq_norm_sq_add_norm_sq_real, norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, InnerProductSpace.gramSchmidt_def, InnerProductSpace.gramSchmidt_orthogonal, InnerProductSpace.span_gramSchmidt, InnerProductSpace.gramSchmidt_ne_zero, InnerProductSpace.gramSchmidtNormed, InnerProductSpace.gramSchmidtNormed_orthonormal, InnerProductSpace.gramSchmidtOrthonormalBasis, stdOrthonormalBasis, OrthonormalBasis.repr, OrthonormalBasis.repr_apply_apply, OrthonormalBasis.sum_repr', OrthonormalBasis.sum_sq_norm_inner_right, Orthonormal.exists_orthonormalBasis_extension, Submodule.orthogonal, Submodule.mem_orthogonal, Submodule.isClosed_orthogonal, Submodule.inf_orthogonal_eq_bot, Submodule.le_orthogonal_orthogonal]
  E1: auto
families: []
requires: [V07, V16.C01, V16.C02, V16.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Orthogonality and orthonormal families

### Overview

Two vectors are orthogonal when their inner product is $0$. This section develops the finite part of the theory of orthogonality: the theorem of Pythagoras, orthonormal families and their linear independence, the inequality of Bessel, and the process of Gram-Schmidt, which turns a linearly independent family into an orthonormal family with the same initial spans. In finite dimension this gives an orthonormal basis, and the coordinates in an orthonormal basis are inner products. The section ends with the orthogonal complement of a subspace, which is closed. The projection onto a subspace, which needs completeness, is the subject of Chapter 7.

### Definitions

In this section $E$ is an inner product space over $\mathbb{K}$.

**Definition (orthogonal).** Vectors $x, y \in E$ are *orthogonal*, written $x \perp y$, if $\langle x, y \rangle = 0$. A family $(v_i)_{i \in \iota}$ is *orthogonal* if $v_i \perp v_j$ for $i \ne j$, and *orthonormal* if also $\|v_i\| = 1$ for each $i$.

::: mathlib
`Orthonormal` · `Mathlib.Analysis.InnerProductSpace.Orthonormal`

`Orthonormal 𝕜 v` for `v : ι → E` is the conjunction `(∀ i, ‖v i‖ = 1) ∧ Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0`. The form with a Kronecker delta is `orthonormal_iff_ite`. A family, not a set, is the basic notion; for a set `s` write `Orthonormal 𝕜 ((↑) : s → E)`. The two parts are `Orthonormal.norm_eq_one` and `Orthonormal.inner_eq_zero`.

<?decl Orthonormal?>
:::

**Definition (orthonormal basis).** If $E$ is finite dimensional, an *orthonormal basis* of $E$ is an orthonormal family that spans $E$.

**Definition (orthogonal complement).** For a subspace $K$ of $E$, $K^\perp = \{y \in E : \langle x, y \rangle = 0 \text{ for all } x \in K\}$.

::: mathlib
`Submodule.orthogonal` · `Mathlib.Analysis.InnerProductSpace.Orthogonal`

`K.orthogonal` is a `Submodule 𝕜 E`. The source writes it with a postfix notation, a raised perpendicular sign after `K`. The membership lemma `Submodule.mem_orthogonal` reads `v ∈ K.orthogonal ↔ ∀ u ∈ K, ⟪u, v⟫_𝕜 = 0`, with the element of `K` on the left. The file proves `Submodule.isClosed_orthogonal`, `Submodule.inf_orthogonal_eq_bot` and `Submodule.le_orthogonal_orthogonal`, which are the three facts of this section.

<?decl Submodule.orthogonal?>
:::

### Theorems and proofs

**Theorem (Pythagoras).** If $x \perp y$ then $\|x + y\|^2 = \|x\|^2 + \|y\|^2$. If $v_1, \dots, v_n$ is orthogonal then $\|\sum_k v_k\|^2 = \sum_k \|v_k\|^2$. Over $\mathbb{R}$ the first equation implies $x \perp y$.

*Proof.* $\|x + y\|^2 = \|x\|^2 + 2\operatorname{Re}\langle x, y \rangle + \|y\|^2$. The middle term vanishes when $x \perp y$, and over $\mathbb{R}$ it is $2\langle x, y \rangle$, so the equation forces $\langle x, y \rangle = 0$. The finite form follows by induction, since $v_n \perp \sum_{k < n} v_k$. $\square$

Over $\mathbb{C}$ the converse fails: $x = 1$ and $y = i$ in $\mathbb{C}$ give $|1 + i|^2 = 2 = 1 + 1$, but $\langle 1, i \rangle = i$. The real forms in Mathlib are `norm_add_sq_eq_norm_sq_add_norm_sq_real` and `norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`, stated with `‖x + y‖ * ‖x + y‖`.

**Theorem (orthonormal families are independent).** An orthonormal family $(v_i)$ is linearly independent. If $x = \sum_{i \in F} c_i v_i$ with $F$ finite, then $c_i = \langle v_i, x \rangle$ and $\|x\|^2 = \sum_{i \in F} |c_i|^2$.

*Proof.* $\langle v_j, \sum_i c_i v_i \rangle = \sum_i c_i\langle v_j, v_i \rangle = c_j$, by linearity in the second argument. If the sum is $0$, each $c_j = 0$. The norm is Pythagoras for the orthogonal family $(c_iv_i)$. $\square$

In Mathlib this is `Orthonormal.linearIndependent`, and the computation of a coefficient is `Orthonormal.inner_right_finsupp` for a finitely supported family of coefficients.

**Theorem (Bessel's inequality).** Let $(v_i)_{i \in \iota}$ be orthonormal and $x \in E$. For each finite $F \subseteq \iota$, $\sum_{i \in F} |\langle v_i, x \rangle|^2 \le \|x\|^2$. Hence $\sum_{i \in \iota} |\langle v_i, x \rangle|^2 \le \|x\|^2$, and $\langle v_i, x \rangle \ne 0$ for at most countably many $i$.

*Proof.* Let $y = \sum_{i \in F} \langle v_i, x \rangle v_i$. For $j \in F$, $\langle v_j, x - y \rangle = \langle v_j, x \rangle - \langle v_j, x \rangle = 0$, so $x - y \perp y$. Pythagoras gives $\|x\|^2 = \|x - y\|^2 + \|y\|^2 \ge \|y\|^2 = \sum_{i \in F} |\langle v_i, x \rangle|^2$. A sum of nonnegative terms whose finite partial sums are bounded is summable, with the same bound. For each $n \ge 1$ at most $n^2\|x\|^2$ indices have $|\langle v_i, x \rangle| \ge 1/n$, so the set of nonzero coefficients is a countable union of finite sets. $\square$

::: mathlib
`Orthonormal.sum_inner_products_le` · `Mathlib.Analysis.InnerProductSpace.Orthonormal`

`hv.sum_inner_products_le x : ∑ i ∈ s, ‖⟪v i, x⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2` for a `Finset` `s`. The infinite form is `Orthonormal.tsum_inner_products_le`, with `∑'`. In Mathlib `∑'` of a family that is not summable is `0`, so the statement with `∑'` alone does not give summability. The summability is the separate lemma `Orthonormal.inner_products_summable`, which Section 3 uses.

<?decl Orthonormal.sum_inner_products_le?>
:::

**Theorem (Gram-Schmidt).** Let $f_1, f_2, \dots$ be a finite or infinite sequence in $E$. Define
$$u_n = f_n - \sum_{k < n,\ u_k \ne 0} \frac{\langle u_k, f_n \rangle}{\|u_k\|^2}\, u_k.$$
Then $(u_n)$ is orthogonal and $\operatorname{span}\{u_1, \dots, u_n\} = \operatorname{span}\{f_1, \dots, f_n\}$ for each $n$. If the $f_n$ are linearly independent, each $u_n \ne 0$ and $e_n = u_n/\|u_n\|$ is orthonormal.

*Proof.* By induction on $n$. Assume $u_1, \dots, u_{n-1}$ orthogonal with the span property. For $j < n$ with $u_j \ne 0$,
$$\langle u_j, u_n \rangle = \langle u_j, f_n \rangle - \frac{\langle u_j, f_n \rangle}{\|u_j\|^2}\langle u_j, u_j \rangle = 0,$$
since the other terms of the sum are orthogonal to $u_j$. If $u_j = 0$, $\langle u_j, u_n \rangle = 0$ trivially. The formula shows $u_n \in f_n + \operatorname{span}\{u_k\}_{k < n} = f_n + \operatorname{span}\{f_k\}_{k < n}$, which gives the span property at $n$. If the $f_k$ are independent, $f_n \notin \operatorname{span}\{f_k\}_{k < n}$, so $u_n \ne 0$. The normalized family is orthogonal with norms $1$. $\square$

::: mathlib
`InnerProductSpace.gramSchmidt` · `Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`

`gramSchmidt 𝕜 f n` for `f : ι → E`, where `ι` is a linear order with `LocallyFiniteOrderBot ι`, such as `ℕ` or `Fin n`. By `gramSchmidt_def` it is `f n - ∑ i < n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n)`: each term is the projection onto the line spanned by an earlier vector, the formula of the text. The theorem is `gramSchmidt_orthogonal`, `span_gramSchmidt` and `gramSchmidt_ne_zero`. The normalized family is `gramSchmidtNormed`, orthonormal by `gramSchmidtNormed_orthonormal` for an independent `f`. All these names sit in the namespace `InnerProductSpace`.

<?decl InnerProductSpace.gramSchmidt?>
:::

**Corollary (orthonormal bases).** A finite dimensional inner product space has an orthonormal basis, and each orthonormal family extends to one. In an orthonormal basis $(e_i)$, $x = \sum_i \langle e_i, x \rangle e_i$ and $\|x\|^2 = \sum_i |\langle e_i, x \rangle|^2$. The map $x \mapsto (\langle e_i, x \rangle)_i$ is a linear isometry of $E$ onto the Euclidean space $\mathbb{K}^\iota$.

*Proof.* Extend the orthonormal family to a basis $f_1, \dots, f_n$ of $E$ by linear algebra, with the given vectors first, and apply Gram-Schmidt. The first vectors are unchanged, since they are already orthonormal, and the result is orthonormal and spans $E$. The expansion and the norm follow from the theorem on independence, and the last statement is a restatement of the norm formula. $\square$

::: mathlib
`OrthonormalBasis` · `Mathlib.Analysis.InnerProductSpace.PiL2`

`OrthonormalBasis ι 𝕜 E`, for a `Fintype ι`, is a structure with one field `repr : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι`. A basis is the isometry to coordinates, and the vectors `b i` are the preimages of the unit vectors. Then `repr_apply_apply` reads `(b.repr v).ofLp i = ⟪b i, v⟫_𝕜`, `sum_repr'` is the expansion and `sum_sq_norm_inner_right` is the norm formula. The basis of the corollary is `stdOrthonormalBasis 𝕜 E`, indexed by `Fin (finrank 𝕜 E)`, and the extension is `Orthonormal.exists_orthonormalBasis_extension`. The basis from a given family is `gramSchmidtOrthonormalBasis`.

<?decl OrthonormalBasis?>
:::

**Theorem (orthogonal complement).** For each subspace $K$ of $E$, $K^\perp$ is a closed subspace, $K \cap K^\perp = \{0\}$ and $K \subseteq K^{\perp\perp}$. Also $K^\perp = \overline{K}^\perp$.

*Proof.* $K^\perp = \bigcap_{x \in K} \ker\langle x, \cdot \rangle$ is an intersection of kernels of bounded functionals, so it is a closed subspace. If $x \in K \cap K^\perp$, then $\langle x, x \rangle = 0$, so $x = 0$. Each $x \in K$ is orthogonal to each $y \in K^\perp$, so $x \in K^{\perp\perp}$. Finally $y \perp K$ implies $y \perp \overline{K}$, by continuity of $x \mapsto \langle x, y \rangle$. $\square$

### Examples

**Example (Gram-Schmidt in $\mathbb{R}^3$).** Let $f_1 = (1, 1, 0)$, $f_2 = (1, 0, 1)$, $f_3 = (0, 1, 1)$. Then $u_1 = f_1$ with $\|u_1\|^2 = 2$. Next $u_2 = f_2 - \tfrac12 u_1 = (\tfrac12, -\tfrac12, 1)$ with $\|u_2\|^2 = \tfrac32$. Finally $\langle u_1, f_3 \rangle = 1$ and $\langle u_2, f_3 \rangle = \tfrac12$, so $u_3 = f_3 - \tfrac12 u_1 - \tfrac13 u_2 = (-\tfrac23, \tfrac23, \tfrac23)$. The checks $\langle u_1, u_3 \rangle = 0$ and $\langle u_2, u_3 \rangle = -\tfrac13 - \tfrac13 + \tfrac23 = 0$ hold.

**Example (Legendre polynomials).** On the real polynomials with $\langle p, q \rangle = \int_{-1}^1 pq$, Gram-Schmidt applied to $1, t, t^2$ gives $u_1 = 1$, $u_2 = t$, since $\int_{-1}^1 t = 0$, and $u_3 = t^2 - \tfrac13$, since $\langle 1, t^2 \rangle / \langle 1, 1 \rangle = \tfrac{2/3}{2}$ and $\langle t, t^2 \rangle = 0$. These are multiples of the Legendre polynomials $1$, $t$ and $\tfrac12(3t^2 - 1)$.

**Example (the trigonometric system).** In $C[0, 2\pi]$ with complex values and $\langle f, g \rangle = \frac{1}{2\pi}\int_0^{2\pi} \bar{f} g$, the functions $e_n(t) = e^{int}$, $n \in \mathbb{Z}$, are orthonormal, since $\int_0^{2\pi} e^{i(m - n)t}\,dt = 0$ for $m \ne n$. Bessel's inequality gives $\sum_n |\hat{f}(n)|^2 \le \frac{1}{2\pi}\int_0^{2\pi}|f|^2$ for the Fourier coefficients $\hat{f}(n) = \langle e_n, f \rangle$.

### The library around it

The vocabulary of this section is split over four files: `Orthonormal` for families, `GramSchmidtOrtho` for the process, `PiL2` for `EuclideanSpace` and `OrthonormalBasis`, and `Orthogonal` for `K.orthogonal`. An `OrthonormalBasis` is not a `Module.Basis`, but `OrthonormalBasis.toBasis` converts it, and `Module.Basis.toOrthonormalBasis` goes back when the basis is orthonormal.

Common errors:

- `Orthonormal 𝕜 v` takes a family. A `Finset` or a `Set` of vectors must be coerced to a family first.
- `gramSchmidt` needs an order on the index type with `LocallyFiniteOrderBot`. For a family indexed by a `Fintype` without an order, choose an equivalence with `Fin n` first.
- `Submodule.mem_orthogonal` puts the element of `K` first in the inner product; `Submodule.mem_orthogonal'` puts it second.

### Exercises

1. (A) Apply Gram-Schmidt to $(1, 0, 1)$, $(0, 1, 1)$ in $\mathbb{R}^3$ and extend the result to an orthonormal basis.
2. (A) Find the orthogonal complement of the line spanned by $(1, 2, 3)$ in $\mathbb{R}^3$.
3. (A) Show that an orthogonal family of nonzero vectors is linearly independent.
4. (B) Let $(e_i)_{i=1}^n$ be orthonormal in $E$ and $x \in E$. Show that $\|x - \sum_i c_i e_i\|$ is smallest exactly when $c_i = \langle e_i, x \rangle$.
5. (B) Show that $K^\perp = K^{\perp\perp\perp}$ for each subspace $K$.
6. (B) Show that the Gram-Schmidt process applied to an orthogonal family returns it unchanged.
7. (C) Let $A$ be an invertible real $n \times n$ matrix. Show that $A = QR$ with $Q$ orthogonal and $R$ upper triangular with positive diagonal, and that this factorization is unique.

### Notes and history

Jørgen Pedersen Gram described the orthogonalization of a sequence of functions in 1883, and Erhard Schmidt gave it in its present form in 1907. Friedrich Wilhelm Bessel used the inequality that has his name in the theory of Fourier series. The files `Mathlib.Analysis.InnerProductSpace.Orthonormal` and `Mathlib.Analysis.InnerProductSpace.Orthogonal` have the authors Zhouhang Zhou, Sébastien Gouëzel and Frédéric Dupuis. The file `Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho` has the authors Jiale Miao, Kevin Buzzard and Alexander Bentkamp.

### Reference

<?reference?>
