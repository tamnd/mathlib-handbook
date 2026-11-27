---
title: Quadratic forms and the polar form
kind: theory
modules:
  - Mathlib.LinearAlgebra.QuadraticForm.Basic
  - Mathlib.LinearAlgebra.QuadraticForm.Isometry
  - Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
  - Mathlib.LinearAlgebra.QuadraticForm.Prod
explains:
  E3: [QuadraticMap, QuadraticMap.polar, QuadraticMap.associated]
  E2: [QuadraticForm, QuadraticMap.map_smul, QuadraticMap.polar_self, QuadraticMap.polarBilin, LinearMap.BilinMap.toQuadraticMap, QuadraticMap.toQuadraticMap_associated, QuadraticMap.associated_toQuadraticMap, QuadraticMap.exists_companion, QuadraticMap.IsometryEquiv, QuadraticMap.Equivalent, QuadraticMap.Isometry, QuadraticMap.prod, QuadraticMap.Anisotropic, QuadraticMap.PosDef, QuadraticMap.weightedSumSquares]
  E1: auto
families: []
requires: [V08.C05, V07.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Quadratic forms and the polar form

### Overview

A quadratic form is a homogeneous polynomial of degree 2, such as $x^2 + 3 x y + y^2$, seen as a function on a module. Each bilinear form $B$ gives one, $x \mapsto B(x, x)$, and conversely each quadratic form $Q$ gives a symmetric bilinear form, its polar
$$\operatorname{polar}_Q(x, y) = Q(x + y) - Q(x) - Q(y).$$
The polar of $B(x, x)$ is $B(x, y) + B(y, x)$, and the polar of $Q$ on the diagonal is $2 Q$. So the two notions agree when $2$ is invertible and differ when it is not, as $\mathbb{F}_2$ shows.

It then defines isometries and equivalence of quadratic forms, orthogonal sums, and the conditions anisotropic and positive definite. The bilinear forms, matrices and isometries of Chapter 5 are used throughout.

### Definitions

Let $R$ be a commutative ring and let $M$ and $N$ be $R$-modules.

**Definition (Quadratic map).** A quadratic map $Q : M \to N$ is a function with
$$Q(a x) = a^2 Q(x) \quad \text{for all } a \in R, \ x \in M,$$
such that the polar $\operatorname{polar}_Q(x, y) = Q(x + y) - Q(x) - Q(y)$ is bilinear. A quadratic form is a quadratic map with $N = R$.

The polar is symmetric by its definition. Taking $a = 0$ gives $Q(0) = 0$, and $a = -1$ gives $Q(-x) = Q(x)$.

::: mathlib
`QuadraticMap` · `Mathlib.LinearAlgebra.QuadraticForm.Basic`

A structure with `toFun`, the field `toFun_smul : toFun (a • x) = (a * a) • toFun x`, and `exists_companion'`: some bilinear `B` has `Q (x + y) = Q x + Q y + B x y`. The companion replaces the polar so that the definition works over a semiring. The case `N = R` is `QuadraticForm R M`.

<?decl QuadraticMap?>
:::

<?decl QuadraticForm?>

<?decl QuadraticMap.map_smul?>

<?decl QuadraticMap.exists_companion?>

::: mathlib
`QuadraticMap.polar` · `Mathlib.LinearAlgebra.QuadraticForm.Basic`

`polar f x y = f (x + y) - f x - f y` for any function `f`, applied as `polar Q x y`. Lemmas such as `polar_add_left` give bilinearity, and `polarBilin Q` bundles the polar as a bilinear map.

<?decl QuadraticMap.polar?>
:::

<?decl QuadraticMap.polarBilin?>

**Definition (Quadratic form of a bilinear form).** For a bilinear map $B : M \times M \to N$, the function $Q_B(x) = B(x, x)$ is a quadratic map.

Indeed $Q_B(a x) = a^2 B(x, x)$, and $Q_B(x + y) - Q_B(x) - Q_B(y) = B(x, y) + B(y, x)$ is bilinear. So $\operatorname{polar}_{Q_B}(x, y) = B(x, y) + B(y, x)$.

<?decl LinearMap.BilinMap.toQuadraticMap?>

**Definition (Isometry and equivalence).** Let $Q_1$ on $M_1$ and $Q_2$ on $M_2$ be quadratic maps to $N$. An isometry is a linear map $f : M_1 \to M_2$ with $Q_2(f x) = Q_1(x)$. An isometric isomorphism is a bijective isometry, and $Q_1$ and $Q_2$ are equivalent if one exists.

An isometry also preserves the polar, since the polar is built from values of $Q$.

::: mathlib
`QuadraticMap.IsometryEquiv` · `Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv`

`Q₁.IsometryEquiv Q₂` extends `M₁ ≃ₗ[R] M₂` by the identity `Q₂ (f x) = Q₁ x`. `QuadraticMap.Equivalent Q₁ Q₂` is `Nonempty (Q₁.IsometryEquiv Q₂)`. The map version `QuadraticMap.Isometry`, with notation `Q₁ →qᵢ Q₂`, lives in `Mathlib.LinearAlgebra.QuadraticForm.Isometry`.

<?decl QuadraticMap.IsometryEquiv?>
:::

<?decl QuadraticMap.Equivalent?>

<?decl QuadraticMap.Isometry?>

**Definition (Orthogonal sum).** For quadratic maps $Q_1$ on $M_1$ and $Q_2$ on $M_2$, the orthogonal sum is $(Q_1 \oplus Q_2)(x_1, x_2) = Q_1(x_1) + Q_2(x_2)$ on $M_1 \times M_2$.

Its polar is $\operatorname{polar}_{Q_1}(x_1, y_1) + \operatorname{polar}_{Q_2}(x_2, y_2)$, so $M_1 \times 0$ and $0 \times M_2$ are orthogonal.

::: mathlib
`QuadraticMap.prod` · `Mathlib.LinearAlgebra.QuadraticForm.Prod`

`Q₁.prod Q₂` is the orthogonal sum on `M₁ × M₂`. The file proves that it respects equivalence (`Equivalent.prod`), and that it is positive definite exactly when both summands are (`posDef_prod_iff`). The version for a family of forms is `QuadraticMap.pi`.

<?decl QuadraticMap.prod?>
:::

**Definition (Weighted sum of squares).** For weights $w_1, \dots, w_n \in R$, the weighted sum of squares is the quadratic form $\sum_i w_i x_i^2$ on $R^n$.

It is the orthogonal sum of the forms $w_i x^2$ on $R$. Section 2 shows that each quadratic form over a field of characteristic not 2 is equivalent to one of them.

<?decl QuadraticMap.weightedSumSquares?>

**Definition (Anisotropic, positive definite).** A quadratic map $Q$ is anisotropic if $Q(x) = 0$ implies $x = 0$. If $N$ is ordered, $Q$ is positive definite if $Q(x) > 0$ for all $x \neq 0$.

A positive definite form is anisotropic. Over $\mathbb{R}$, the form $x^2 + y^2$ is positive definite and $x^2 - y^2$ is not anisotropic, since $Q(1, 1) = 0$.

<?decl QuadraticMap.Anisotropic?>

<?decl QuadraticMap.PosDef?>

### Theorems and proofs

**Proposition (Polar on the diagonal).** For each quadratic map, $\operatorname{polar}_Q(x, x) = 2 Q(x)$.

*Proof.* $\operatorname{polar}_Q(x, x) = Q(2 x) - 2 Q(x) = 4 Q(x) - 2 Q(x) = 2 Q(x)$. $\square$

<?decl QuadraticMap.polar_self?>

**Proposition (Quadratic forms in coordinates).** Let $M$ be free with basis $e_1, \dots, e_n$ and let $Q$ be a quadratic form. Then
$$Q\Big(\sum_i x_i e_i\Big) = \sum_i Q(e_i) x_i^2 + \sum_{i < j} \operatorname{polar}_Q(e_i, e_j) x_i x_j.$$
So $Q$ is the form $Q_B$ of the bilinear form $B$ with the upper triangular matrix $B_{ii} = Q(e_i)$, $B_{ij} = \operatorname{polar}_Q(e_i, e_j)$ for $i < j$, and $B_{ij} = 0$ for $i > j$.

*Proof.* Induction on $n$. For $n = 1$, $Q(x_1 e_1) = x_1^2 Q(e_1)$. For the step, write $x = y + x_n e_n$ with $y = \sum_{i < n} x_i e_i$. By the definition of the polar and its bilinearity,
$$Q(x) = Q(y) + x_n^2 Q(e_n) + \sum_{i < n} x_i x_n \operatorname{polar}_Q(e_i, e_n),$$
and the induction hypothesis expands $Q(y)$. The form $Q_B$ of the given matrix has the same expansion, because $B(x, x) = \sum_{i \le j} B_{ij} x_i x_j$ for an upper triangular $B$. $\square$

So each quadratic form on a free module is the diagonal of a bilinear form, possibly not symmetric.

**Theorem (Polarization).** Suppose that $2$ is invertible in $R$. For a quadratic map $Q$, put
$$B_Q(x, y) = \tfrac{1}{2} \operatorname{polar}_Q(x, y).$$
Then $B_Q$ is a symmetric bilinear map with $B_Q(x, x) = Q(x)$. The maps $Q \mapsto B_Q$ and $B \mapsto Q_B$ are inverse bijections between quadratic maps and symmetric bilinear maps $M \times M \to N$.

*Proof.* $B_Q$ is bilinear and symmetric because the polar is. By the proposition, $B_Q(x, x) = \frac{1}{2} \cdot 2 Q(x) = Q(x)$, so $Q_{B_Q} = Q$. Conversely, let $B$ be symmetric. Then $\operatorname{polar}_{Q_B}(x, y) = B(x, y) + B(y, x) = 2 B(x, y)$, so $B_{Q_B} = B$. $\square$

The symmetric form $B_Q$ is the associated bilinear form of $Q$. Its matrix in a basis is the matrix of $Q$; for $Q = \sum_{i \le j} a_{ij} x_i x_j$ it has the diagonal entries $a_{ii}$ and the entries $a_{ij} / 2$ off the diagonal.

::: mathlib
`QuadraticMap.associated` · `Mathlib.LinearAlgebra.QuadraticForm.Basic`

The linear map $Q \mapsto B_Q$ under `[Invertible (2 : R)]`. The identity `toQuadraticMap_associated` is $Q_{B_Q} = Q$, and `associated_toQuadraticMap` computes $B_{Q_B} = ⅟2 \cdot (B + B^{\mathrm{flip}})$. Without `Invertible 2`, use `polarBilin Q`.

<?decl QuadraticMap.associated?>
:::

<?decl QuadraticMap.toQuadraticMap_associated?>

<?decl QuadraticMap.associated_toQuadraticMap?>

**Proposition (Characteristic 2).** Let $K$ be a field of characteristic 2 and $M$ a $K$-vector space. Then the polar of each quadratic form on $M$ is alternating. If $M \neq 0$, the map $Q \mapsto \operatorname{polar}_Q$ is not injective.

*Proof.* By the proposition above, $\operatorname{polar}_Q(x, x) = 2 Q(x) = 0$. For the second claim, pick a nonzero linear form $\lambda$ on $M$ (Volume 7, Chapter 6) and put $Q(x) = \lambda(x)^2$. It is the diagonal of the bilinear form $\lambda(x) \lambda(y)$, so it is a quadratic form, and its polar is $2 \lambda(x) \lambda(y) = 0$. Some $x$ has $\lambda(x) \neq 0$, so $Q(x) \neq 0$ in the field $K$. So $Q$ and $0$ are different forms with the same polar. $\square$

### Examples

**Example (Matrix of a quadratic form).** Over $\mathbb{Q}$ let $Q(x, y) = x^2 + 3 x y + y^2$. Its polar is
$$\operatorname{polar}_Q((x, y), (x', y')) = 2 x x' + 3 (x y' + x' y) + 2 y y',$$
and its associated form has the matrix $\begin{pmatrix} 1 & 3/2 \\ 3/2 & 1 \end{pmatrix}$, while the upper triangular matrix $\begin{pmatrix} 1 & 3 \\ 0 & 1 \end{pmatrix}$ of the coordinate proposition gives the same quadratic form.

**Counterexample (The form $x y$ over $\mathbb{F}_2$).** On $\mathbb{F}_2^2$ let $Q(x, y) = x y$. It is the diagonal of the bilinear form $B(v, v') = x y'$, so it is a quadratic form. Its polar is
$$\operatorname{polar}_Q((x, y), (x', y')) = (x + x')(y + y') - x y - x' y' = x y' + x' y.$$
On the diagonal the polar is $2 x y = 0$, while $Q(1, 1) = 1$: the polar does not recover $Q$, and no division by $2$ is possible. The form $Q'(x, y) = x y + x^2$ has the same polar, since $x^2$ has polar $2 x x' = 0$; so the polar does not determine $Q$. Finally, $Q$ is not $B'(v, v)$ for any symmetric $B'$. For such $B'$ with entries $b_{ij}$, $B'(v, v) = b_{11} x^2 + 2 b_{12} x y + b_{22} y^2 = b_{11} x^2 + b_{22} y^2$. From $Q(1, 0) = 0$ and $Q(0, 1) = 0$ follow $b_{11} = b_{22} = 0$, and then $B'((1, 1), (1, 1)) = 0 \neq Q(1, 1)$. In characteristic 2, quadratic forms are a strictly richer structure than symmetric bilinear forms.

**Example (Anisotropy depends on the field).** The form $x^2 - 2 y^2$ is anisotropic over $\mathbb{Q}$: if $x^2 = 2 y^2$ with $y \neq 0$, then $(x / y)^2 = 2$, which has no rational solution. Over $\mathbb{R}$ the vector $(\sqrt 2, 1)$ is isotropic.

### The library around it

The matrices `QuadraticForm.toMatrix'` and the discriminant are in `Mathlib.LinearAlgebra.QuadraticForm.Basic`, the isometries in the two isometry files, the orthogonal sums in `.Prod`. Section 2 diagonalizes; Chapter 7 builds the Clifford algebra.

<?decl QuadraticForm.discr?>

### Exercises

1. (A) Find the polar and the matrix of the associated form of $Q(x, y, z) = x^2 - y z$ over $\mathbb{Q}$. Hint: the off-diagonal entries are halves of the coefficients.
2. (A) Show that $Q(x + y + z) - Q(x + y) - Q(y + z) - Q(z + x) + Q(x) + Q(y) + Q(z) = 0$ for each quadratic map. Hint: expand with the polar.
3. (A) Show that an isometry $f$ of quadratic maps satisfies $\operatorname{polar}_{Q_2}(f x, f y) = \operatorname{polar}_{Q_1}(x, y)$. Hint: $f$ is additive.
4. (B) Show that $(Q_1 \oplus Q_2)$ is anisotropic only if $Q_1$ and $Q_2$ are, and that $x^2 \oplus (-y^2)$ is not anisotropic. Hint: restrict to $M_1 \times 0$.
5. (B) Over $\mathbb{F}_2$ list all quadratic forms on $\mathbb{F}_2^2$ and their polars. How many quadratic forms are there, and how many alternating forms? Hint: a quadratic form is $a x^2 + b x y + c y^2$.
6. (B) Show that the parallelogram law $Q(x + y) + Q(x - y) = 2 Q(x) + 2 Q(y)$ holds for each quadratic map. Hint: compute $\operatorname{polar}_Q(x, y) + \operatorname{polar}_Q(x, -y)$.
7. (B) Let $2$ be invertible. Show that $Q$ is anisotropic if and only if its associated form has no isotropic vector. Hint: $B_Q(x, x) = Q(x)$.
8. (C) Over a field $K$ of characteristic 2, show that the polar of each quadratic form on $K^n$ is alternating, and that every alternating form on $K^n$ is the polar of some quadratic form. Hint: for an alternating form with matrix $A$, take the strictly upper triangular part of $A$ as in the coordinate proposition.

### Notes and history

Quadratic forms in two variables with integer coefficients were studied by Lagrange and by Gauss in the "Disquisitiones Arithmeticae" of 1801. The definition through the polar, which works in characteristic 2, is the modern one; in the theory of algebraic groups and in coding theory the characteristic 2 case is essential.

### Reference

<?reference?>
