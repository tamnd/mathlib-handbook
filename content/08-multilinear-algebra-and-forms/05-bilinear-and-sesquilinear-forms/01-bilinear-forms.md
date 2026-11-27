---
title: Bilinear forms
kind: theory
modules:
  - Mathlib.LinearAlgebra.BilinearForm.Basic
  - Mathlib.LinearAlgebra.BilinearForm.Properties
  - Mathlib.LinearAlgebra.SesquilinearForm.Basic
explains:
  E3: [LinearMap.BilinForm.IsSymm, LinearMap.BilinForm.Nondegenerate]
  E2: [LinearMap.BilinForm.IsRefl, LinearMap.BilinForm.IsAlt, LinearMap.BilinForm.IsAlt.neg_eq, LinearMap.BilinForm.IsSymm.polarization, LinearMap.BilinForm.flip, LinearMap.BilinForm.isSymm_iff_flip, LinearMap.BilinForm.restrict, LinearMap.BilinForm.add_left, LinearMap.SeparatingLeft, LinearMap.Nondegenerate, LinearMap.IsSymm, LinearMap.isAlt_iff_eq_neg_flip, LinearMap.BilinForm.toDual, LinearMap.BilinForm.dualBasis, LinearMap.BilinForm.Nondegenerate.ker_eq_bot]
  E1: auto
families: []
requires: [V08.C01, V07.C03, V07.C04, V07.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bilinear forms

### Overview

A bilinear form is a bilinear map with values in the ring of scalars. Examples are the dot product on $\mathbb{R}^n$, the trace form $(X, Y) \mapsto \operatorname{tr}(X Y)$ on matrices and the determinant form $(x, y) \mapsto x_1 y_2 - x_2 y_1$ on $K^2$.

This section defines the matrix of a form and its change of basis, symmetric, alternating, reflexive and nondegenerate forms, and the identification of $V$ with its dual by a nondegenerate form. It proves that a reflexive form is symmetric or alternating, and ends with sesquilinear and Hermitian forms.

Chapter 1 and Volume 7, Chapters 3, 4 and 6 are used without comment.

### Definitions

Let $R$ be a commutative ring and let $M$ be an $R$-module.

**Definition (Bilinear form).** A bilinear form on $M$ is a map $B : M \times M \to R$ that is linear in each argument when the other is fixed.

In Mathlib a form is `LinearMap.BilinForm R M`, an abbreviation for `M →ₗ[R] M →ₗ[R] R`, so `B x y` is $B(x, y)$; the rules `add_left` and its relatives are `simp` lemmas.

<?decl LinearMap.BilinForm?>

<?decl LinearMap.BilinForm.add_left?>

**Definition (Matrix of a form).** Let $e_1, \dots, e_n$ be a basis of a free module $M$. The matrix of $B$ in this basis is the $n \times n$ matrix $A$ with $A_{ij} = B(e_i, e_j)$.

By bilinearity, for $x = \sum_i x_i e_i$ and $y = \sum_j y_j e_j$,
$$B(x, y) = \sum_{i, j} x_i A_{ij} y_j = x^{\mathsf{T}} A y,$$
with $x, y$ the coordinate columns.

::: mathlib
`LinearMap.BilinForm.toMatrix` · `Mathlib.LinearAlgebra.Matrix.BilinearForm`

The linear equivalence from forms to `Matrix n n R` for a finite basis `b`; its inverse is `Matrix.toBilin b`.

<?decl LinearMap.BilinForm.toMatrix?>
:::

**Definition (Symmetric, alternating, reflexive).** A form $B$ is symmetric if $B(x, y) = B(y, x)$, alternating if $B(x, x) = 0$, skew-symmetric if $B(x, y) = -B(y, x)$, and reflexive if $B(x, y) = 0$ implies $B(y, x) = 0$, for all $x, y$.

Symmetric and alternating forms are reflexive. A form is symmetric exactly when $A^{\mathsf{T}} = A$.

::: mathlib
`LinearMap.BilinForm.IsSymm` · `Mathlib.LinearAlgebra.BilinearForm.Properties`

A structure with one field `eq : ∀ x y, B x y = B y x`. By `isSymm_iff_flip`, $B$ is symmetric when it equals `B.flip`, whose matrix is the transpose.

<?decl LinearMap.BilinForm.IsSymm?>
:::

<?decl LinearMap.BilinForm.flip?>

<?decl LinearMap.BilinForm.isSymm_iff_flip?>

<?decl LinearMap.BilinForm.IsAlt?>

<?decl LinearMap.BilinForm.IsRefl?>

**Definition (Nondegenerate form).** The left kernel of $B$ is $\{x : B(x, y) = 0 \text{ for all } y\}$ and the right kernel is $\{y : B(x, y) = 0 \text{ for all } x\}$. The form is left-separating if its left kernel is $0$, right-separating if its right kernel is $0$, and nondegenerate if it is both.

For a reflexive form the two kernels are equal. This common kernel is the radical of $B$.

::: mathlib
`LinearMap.BilinForm.Nondegenerate` · `Mathlib.LinearAlgebra.BilinearForm.Properties`

The conjunction `SeparatingLeft B ∧ SeparatingRight B`. The two halves are equivalent in finite dimension over a field, but not in general.

<?decl LinearMap.BilinForm.Nondegenerate?>
:::

<?decl LinearMap.SeparatingLeft?>

<?decl LinearMap.Nondegenerate?>

<?decl LinearMap.BilinForm.Nondegenerate.ker_eq_bot?>

<?decl LinearMap.BilinForm.restrict?>

### Theorems and proofs

**Proposition (Change of basis).** Let $e$ and $f$ be two bases of $M$ with $n$ elements, and let $P$ be the matrix with $f_k = \sum_i P_{ik} e_i$. If $A$ is the matrix of $B$ in $e$, then the matrix of $B$ in $f$ is $P^{\mathsf{T}} A P$.

*Proof.* By bilinearity,
$$B(f_k, f_l) = \sum_{i, j} P_{ik} P_{jl} B(e_i, e_j) = \sum_{i, j} (P^{\mathsf{T}})_{ki} A_{ij} P_{jl} = (P^{\mathsf{T}} A P)_{kl}. \qquad \square$$

Matrices $A$ and $P^{\mathsf{T}} A P$ with $P$ invertible are called congruent; congruence is not similarity.

**Corollary (Discriminant).** Over a field $K$, $\det(P^{\mathsf{T}} A P) = (\det P)^2 \det A$. So the rank of $A$ and the class of $\det A$ in $K / (K^{\times})^2$ do not depend on the basis.

*Proof.* The formula follows from $\det P^{\mathsf{T}} = \det P$ and the multiplicativity of the determinant. The rank does not change under the multiplication by the invertible matrices $P^{\mathsf{T}}$ and $P$ (Volume 7, Chapter 3). $\square$

<?decl LinearMap.BilinForm.toMatrix_comp?>

**Proposition (Alternating and skew-symmetric).** An alternating form is skew-symmetric. If $2$ is not a zero divisor in $R$, a skew-symmetric form is alternating.

*Proof.* Let $B$ be alternating. Then
$$0 = B(x + y, x + y) = B(x, x) + B(x, y) + B(y, x) + B(y, y) = B(x, y) + B(y, x).$$
Conversely, if $B$ is skew-symmetric, then $B(x, x) = -B(x, x)$, so $2 B(x, x) = 0$, and $B(x, x) = 0$ when $2$ is not a zero divisor. $\square$

::: mathlib
`LinearMap.BilinForm.IsAlt.neg_eq` · `Mathlib.LinearAlgebra.BilinearForm.Properties`

`hB.neg_eq x y : -B x y = B y x`. The converse is `LinearMap.isAlt_iff_eq_neg_flip`, under `NoZeroDivisors R` and `CharZero R`.

<?decl LinearMap.BilinForm.IsAlt.neg_eq?>
:::

<?decl LinearMap.isAlt_iff_eq_neg_flip?>

**Proposition (Polarization).** If $2$ is invertible in $R$ and $B$ is symmetric, then
$$B(x, y) = \tfrac{1}{2} \big( B(x + y, x + y) - B(x, x) - B(y, y) \big).$$
So a symmetric form is determined by its values $B(x, x)$.

*Proof.* Expand $B(x + y, x + y) = B(x, x) + B(x, y) + B(y, x) + B(y, y)$ and use $B(y, x) = B(x, y)$. $\square$

<?decl LinearMap.BilinForm.IsSymm.polarization?>

**Theorem (Nondegeneracy and the dual).** Let $V$ be a vector space of finite dimension $n$ over a field $K$, let $B$ be a form on $V$ and let $A$ be its matrix in a basis. The following are equivalent: (1) $B$ is left-separating; (2) $B$ is right-separating; (3) $\det A \neq 0$. When they hold, the map $V \to V^*$, $x \mapsto B(x, -)$ is an isomorphism.

*Proof.* Write $x$ and $y$ in coordinates. Then $B(x, e_j) = (A^{\mathsf{T}} x)_j$, so $x$ is in the left kernel if and only if $A^{\mathsf{T}} x = 0$. Also $B(e_i, y) = (A y)_i$, so $y$ is in the right kernel if and only if $A y = 0$. A square matrix over a field has a zero kernel exactly when its determinant is not zero (Volume 7, Chapter 4), and $\det A^{\mathsf{T}} = \det A$. The map $x \mapsto B(x, -)$ has the left kernel as its kernel, so it is injective, and $\dim V^* = \dim V$ (Volume 7, Chapter 6). $\square$

::: mathlib
`LinearMap.BilinForm.toDual` · `Mathlib.LinearAlgebra.BilinearForm.Properties`

For nondegenerate `B` on a finite-dimensional space, `B.toDual hB` is the isomorphism $V \simeq V^*$.

<?decl LinearMap.BilinForm.toDual?>
:::

<?decl LinearMap.BilinForm.nondegenerate_iff_det_ne_zero?>

<?decl LinearMap.BilinForm.dualBasis?>

**Theorem (Reflexive forms).** Let $B$ be a reflexive form on a module $M$ over an integral domain $R$. Then $B$ is symmetric or alternating.

*Proof.* Fix $x, y, z \in M$. The vector $w = B(x, y) z - B(x, z) y$ has $B(x, w) = 0$. By reflexivity $B(w, x) = 0$, that is,
$$B(x, y) B(z, x) = B(x, z) B(y, x) \quad \text{for all } x, y, z. \tag{1}$$
With $z = x$, (1) gives $B(x, x) \big( B(x, y) - B(y, x) \big) = 0$. Since $R$ is a domain,
$$B(x, x) = 0 \quad \text{or} \quad B(x, y) = B(y, x) \text{ for all } y. \tag{2}$$
Suppose that $B$ is not symmetric: there are $u, v$ with $B(u, v) \neq B(v, u)$. By (2), $B(u, u) = 0$ and $B(v, v) = 0$. Suppose also that some $w$ has $B(w, w) \neq 0$. By (2), $B(w, y) = B(y, w)$ for all $y$. Now (1) with $(x, y, z) = (u, v, w)$ gives $B(u, v) B(w, u) = B(u, w) B(v, u)$, and with $B(w, u) = B(u, w)$ this is $B(u, w) \big( B(u, v) - B(v, u) \big) = 0$. So $B(u, w) = B(w, u) = 0$. In the same way (1) with $(x, y, z) = (v, u, w)$ gives $B(v, w) = B(w, v) = 0$. Then $B(u + w, v) = B(u, v)$ and $B(v, u + w) = B(v, u)$, so $u + w$ is not symmetric to $v$, and (2) gives $B(u + w, u + w) = 0$. But
$$B(u + w, u + w) = B(u, u) + B(u, w) + B(w, u) + B(w, w) = B(w, w) \neq 0,$$
a contradiction. So $B(w, w) = 0$ for all $w$, and $B$ is alternating. $\square$

The index of this edition has no declaration for this theorem; the library states results for `IsRefl`, `IsSymm` or `IsAlt` forms as needed.

**Definition (Sesquilinear and Hermitian forms).** Let $\sigma$ be an involutive automorphism of $R$, such as complex conjugation. A sesquilinear form is biadditive with $B(a x, y) = \sigma(a) B(x, y)$ and $B(x, a y) = a B(x, y)$. It is Hermitian if $B(y, x) = \sigma(B(x, y))$.

In a basis $B(x, y) = \sigma(x)^{\mathsf{T}} A y$, and $B$ is Hermitian exactly when $\sigma(A)^{\mathsf{T}} = A$. Positive definite Hermitian forms are inner products, the subject of Volume 16.

::: mathlib
`LinearMap.IsSymm` · `Mathlib.LinearAlgebra.SesquilinearForm.Basic`

A sesquilinear form is `B : M →ₛₗ[I] M →ₗ[R] R`, semilinear in the first argument. `LinearMap.IsSymm B` asks `I (B x y) = B y x`.

<?decl LinearMap.IsSymm?>
:::

### Examples

**Example (The determinant form).** On $K^2$ the form $\omega(x, y) = x_1 y_2 - x_2 y_1$ has the matrix $\begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$ with determinant $1$. It is alternating and nondegenerate. For a matrix $P$, $\omega(P x, P y) = \det(P) \, \omega(x, y)$, since $\omega(x, y)$ is the determinant of the matrix with the columns $x$ and $y$.

**Counterexample (Skew-symmetric but not alternating).** Over $\mathbb{F}_2$ the form $B(x, y) = x y$ on $\mathbb{F}_2$ is symmetric, and since $-1 = 1$ it is also skew-symmetric. But $B(1, 1) = 1 \neq 0$, so it is not alternating. The hypothesis on $2$ in the proposition is necessary.

**Counterexample (Left- but not right-separating).** Let $V$ have the basis $e_0, e_1, e_2, \dots$ and let $B(e_i, e_j) = 1$ if $j = i + 1$ and $0$ otherwise. For $x = \sum a_i e_i$ and $j \ge 1$, $B(x, e_j) = a_{j-1}$, so the left kernel is $0$. But $B(e_i, e_0) = 0$ for all $i$, so $e_0$ is in the right kernel. So finite dimension is necessary in the theorem on nondegeneracy.

### The library around it

The files are `Mathlib.LinearAlgebra.BilinearForm.Basic`, `.Properties` and `Mathlib.LinearAlgebra.SesquilinearForm.Basic`. Most results exist both for `LinearMap.BilinForm` and for general bilinear maps.

### Exercises

1. (A) Write the matrix of the trace form $B(X, Y) = \operatorname{tr}(X Y)$ on the $2 \times 2$ matrices in the basis $E_{11}, E_{12}, E_{21}, E_{22}$. Is it symmetric? Nondegenerate? Hint: $\operatorname{tr}(E_{ij} E_{kl}) = 1$ exactly when $j = k$ and $i = l$.
2. (A) Show that each form over a ring in which $2$ is invertible is the sum of a symmetric and a skew-symmetric form, in a unique way. Hint: $B = \frac{1}{2}(B + B^{\mathrm{flip}}) + \frac{1}{2}(B - B^{\mathrm{flip}})$.
3. (A) Show that the forms $x_1 y_1 + x_2 y_2$ and $2 x_1 y_1 + 3 x_2 y_2$ on $\mathbb{Q}^2$ are not congruent. Hint: compare the determinants modulo squares.
4. (B) Show that the matrix of an alternating form in any basis is skew-symmetric with zero diagonal, also over $\mathbb{F}_2$. Deduce that a nondegenerate alternating form on $K^n$ needs $n$ even when $2 \neq 0$ in $K$. Hint: $\det A^{\mathsf{T}} = \det(-A)$.
5. (B) Let $B$ be a form on a finite-dimensional space $V$ over a field. Show that the left and right kernels have the same dimension, even when they are different. Hint: $\operatorname{rank} A = \operatorname{rank} A^{\mathsf{T}}$.
6. (C) Show that, over every field, the alternating forms on $K^n$ form a space of dimension $n(n-1)/2$ and the symmetric forms a space of dimension $n(n+1)/2$. Hint: use the matrices, and Exercise 4 for the alternating case.

### Notes and history

Bilinear forms arose from quadratic forms, the subject of Chapter 6, and Sylvester's law of inertia of 1852 is a central early result. The split of reflexive forms into symmetric and alternating ones is the base of the theory of the classical groups.

### Reference

<?reference?>
