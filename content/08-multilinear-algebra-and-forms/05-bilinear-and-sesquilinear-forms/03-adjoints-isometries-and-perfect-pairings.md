---
title: Adjoints, isometries and perfect pairings
kind: theory
modules:
  - Mathlib.LinearAlgebra.BilinearForm.Hom
  - Mathlib.LinearAlgebra.BilinearForm.Isometry
  - Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
  - Mathlib.LinearAlgebra.PerfectPairing.Basic
  - Mathlib.LinearAlgebra.PerfectPairing.Restrict
  - Mathlib.LinearAlgebra.BilinearForm.DualLattice
explains:
  E3: [LinearMap.BilinForm.IsometryEquiv, LinearMap.IsPerfPair]
  E2: [LinearMap.BilinForm.comp, LinearMap.BilinForm.congr, LinearMap.BilinForm.compLeft, LinearMap.BilinForm.Isometry, LinearMap.BilinForm.Equivalent, LinearMap.BilinForm.isometryEquivOfCompLinearEquiv, LinearMap.BilinForm.ext_basis, LinearMap.BilinForm.sum_repr_mul_repr_mul, LinearMap.toPerfPair, LinearMap.IsPerfPair.of_injective, LinearMap.IsPerfPair.nondegenerate, Module.finrank_of_isPerfPair, LinearMap.IsPerfPair.dualEval]
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

## Adjoints, isometries and perfect pairings

### Overview

A form gives each linear map a partner, its adjoint, defined by moving the map from one side of the form to the other. It also gives a group, the linear maps that preserve the form. For the dot product these are the transpose and the orthogonal group; for the determinant form on $K^2$ the group is $\mathrm{SL}_2(K)$.

Using $V \simeq V^*$ from Section 1, this section constructs adjoints, describes isometries by $P^{\mathsf{T}} A P = A$, and ends with perfect pairings of two modules.

### Definitions

Let $R$ be a commutative ring, and let $B_1$ on $M_1$ and $B_2$ on $M_2$ be bilinear forms.

**Definition (Adjoint pair).** Let $B$ be a form on $M$. Linear maps $\psi, \varphi : M \to M$ form an adjoint pair if
$$B(\psi x, y) = B(x, \varphi y) \quad \text{for all } x, y \in M.$$
Then $\psi$ is a left adjoint of $\varphi$, and $\varphi$ is a right adjoint of $\psi$.

<?decl LinearMap.IsAdjointPair?>

**Definition (Isometry).** An isometry $f : (M_1, B_1) \to (M_2, B_2)$ is a linear map with $B_2(f x, f y) = B_1(x, y)$ for all $x, y$. An isometric isomorphism is a bijective isometry. The forms are equivalent if an isometric isomorphism exists.

The isometric isomorphisms of $(M, B)$ to itself form a group, the orthogonal group $\mathrm{O}(B)$. When $B$ is alternating it is also called the symplectic group $\mathrm{Sp}(B)$.

::: mathlib
`LinearMap.BilinForm.IsometryEquiv` · `Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv`

`B₁.IsometryEquiv B₂` is a structure that extends `M₁ ≃ₗ[R] M₂` by the field `map_app'`, the identity `B₂ (f x) (f y) = B₁ x y`. `B₁.Equivalent B₂` is the proposition `Nonempty (B₁.IsometryEquiv B₂)`. The map version `LinearMap.BilinForm.Isometry` has no bijectivity.

<?decl LinearMap.BilinForm.IsometryEquiv?>
:::

<?decl LinearMap.BilinForm.Equivalent?>

<?decl LinearMap.BilinForm.Isometry?>

<?decl LinearMap.IsOrthogonal?>

**Definition (Pulling back a form).** For a form $B$ on $M'$ and linear maps $l, r : M \to M'$, the form $B(l x, r y)$ on $M$ is the pullback of $B$ along $l$ and $r$. For an isomorphism $e : M \simeq M'$, transport is the form $B(e^{-1} x, e^{-1} y)$ on $M'$ for $B$ on $M$.

::: mathlib
`LinearMap.BilinForm.comp` · `Mathlib.LinearAlgebra.BilinearForm.Hom`

`B.comp l r` is the pullback `fun x y ↦ B (l x) (r y)`, and `B.compLeft f` is the case `r = id`. The transport `LinearMap.BilinForm.congr e` is a linear equivalence between the spaces of forms. For a linear equivalence `f`, `B.isometryEquivOfCompLinearEquiv f` is an isometric isomorphism between `B` and its pullback `B.comp f f`.

<?decl LinearMap.BilinForm.comp?>
:::

<?decl LinearMap.BilinForm.compLeft?>

<?decl LinearMap.BilinForm.congr?>

<?decl LinearMap.BilinForm.isometryEquivOfCompLinearEquiv?>

**Definition (Perfect pairing).** Let $M$ and $N$ be $R$-modules. A bilinear map $p : M \times N \to R$ is a perfect pairing if both maps $M \to N^*$, $x \mapsto p(x, -)$, and $N \to M^*$, $y \mapsto p(-, y)$, are bijective.

A form $B$ on $V$ is a pairing of $V$ with itself; Section 1 shows that a nondegenerate form on a finite-dimensional space is perfect.

::: mathlib
`LinearMap.IsPerfPair` · `Mathlib.LinearAlgebra.PerfectPairing.Basic`

A class on `p : M →ₗ[R] N →ₗ[R] R` with the two fields `bijective_left : Bijective p` and `bijective_right : Bijective p.flip`. The equivalence `p.toPerfPair : M ≃ₗ[R] Module.Dual R N` is the bijection of the first field.

<?decl LinearMap.IsPerfPair?>
:::

<?decl LinearMap.toPerfPair?>

### Theorems and proofs

**Proposition (Forms on a basis).** Two forms that agree on all pairs $(e_i, e_j)$ of a basis are equal, and $B(x, y) = \sum_{i, j} x_i y_j B(e_i, e_j)$ for the coordinates $x_i$ and $y_j$.

*Proof.* The formula is bilinearity applied to $x = \sum_i x_i e_i$ and $y = \sum_j y_j e_j$. The right side depends only on the values $B(e_i, e_j)$. $\square$

<?decl LinearMap.BilinForm.sum_repr_mul_repr_mul?>

<?decl LinearMap.BilinForm.ext_basis?>

From here on, $V$ is a vector space of finite dimension over a field $K$ and $B$ is a nondegenerate form on $V$ with matrix $A$ in a basis.

**Theorem (Existence of adjoints).** Each linear map $\varphi : V \to V$ has a unique left adjoint $\psi$. If $\Phi$ and $\Psi$ are the matrices of $\varphi$ and $\psi$, then $\Psi = (A^{\mathsf{T}})^{-1} \Phi^{\mathsf{T}} A^{\mathsf{T}}$.

*Proof.* Fix $x$. The map $y \mapsto B(x, \varphi y)$ is a linear form on $V$. By Section 1, the map $\beta : V \to V^*$, $z \mapsto B(z, -)$, is an isomorphism, so there is a unique $\psi x \in V$ with $B(\psi x, y) = B(x, \varphi y)$ for all $y$. Explicitly $\psi x = \beta^{-1}(B(x, -) \circ \varphi)$, a composite of linear maps, so $\psi$ is linear. Uniqueness: if $\psi'$ is another left adjoint, then $B(\psi x - \psi' x, y) = 0$ for all $y$, so $\psi x = \psi' x$. For the matrix, $B(\psi x, y) = x^{\mathsf{T}} \Psi^{\mathsf{T}} A y$ and $B(x, \varphi y) = x^{\mathsf{T}} A \Phi y$. These agree for all $x, y$ if and only if $\Psi^{\mathsf{T}} A = A \Phi$, that is $\Psi^{\mathsf{T}} = A \Phi A^{-1}$; transposing gives the formula. $\square$

<?decl LinearMap.BilinForm.leftAdjointOfNondegenerate?>

<?decl LinearMap.BilinForm.isAdjointPair_iff_eq_of_nondegenerate?>

In the same way each $\psi$ has a unique right adjoint. For the dot product $A = I$, and the adjoint is the transpose.

**Proposition (Symmetric and alternating forms).** Suppose $B(y, x) = \varepsilon B(x, y)$ for all $x, y$, with $\varepsilon = 1$ (symmetric) or $\varepsilon = -1$ (skew-symmetric). Then the left and right adjoints of each map agree, and the adjoint $\varphi^*$ satisfies $(\varphi^*)^* = \varphi$.

*Proof.* Let $\psi$ be the left adjoint of $\varphi$. Then $B(\varphi y, x) = \varepsilon B(x, \varphi y) = \varepsilon B(\psi x, y) = B(y, \psi x)$, so $\varphi$ is a left adjoint of $\psi$, and $\psi$ is a right adjoint of $\varphi$. So left and right adjoints agree, and the adjoint of $\psi = \varphi^*$ is $\varphi$. $\square$

**Theorem (Isometries).** Let $B$ be any form on a module $M$ over $R$ and let $g : M \to M$ be a linear bijection. Then $g$ is an isometry if and only if $g$ is a left adjoint of $g^{-1}$. In a basis with matrix $A$ for $B$ and $P$ for $g$, $g$ is an isometry if and only if $P^{\mathsf{T}} A P = A$. If $R$ is a field and $B$ is nondegenerate, then $\det P = \pm 1$.

*Proof.* If $g$ is an isometry, then $B(g x, y) = B(g x, g g^{-1} y) = B(x, g^{-1} y)$. Conversely, if $B(g x, y) = B(x, g^{-1} y)$ for all $x, y$, then with $y = g z$ this is $B(g x, g z) = B(x, z)$. The matrix of $(x, y) \mapsto B(g x, g y)$ is $P^{\mathsf{T}} A P$ by the change of basis rule of Section 1, and a form is determined by its matrix. Taking determinants, $(\det P)^2 \det A = \det A$, and $\det A \neq 0$ for a nondegenerate form, so $(\det P)^2 = 1$. $\square$

<?decl LinearEquiv.isAdjointPair_symm_iff?>

<?decl LinearMap.isOrthogonal_of_forall_apply_same?>

<?decl Matrix.orthogonalGroup?>

<?decl Matrix.symplecticGroup?>

<?decl SymplecticGroup.det_eq_one?>

**Theorem (Perfect pairings over a field).** Let $M$ and $N$ be vector spaces over $K$ with $M$ finite-dimensional, and let $p : M \times N \to K$ be bilinear. Then $p$ is perfect if and only if both maps $M \to N^*$ and $N \to M^*$ are injective. In this case $\dim M = \dim N$.

*Proof.* A bijection is injective. Conversely, suppose both maps are injective. Since $N \to M^*$ is injective and $\dim M^* = \dim M$ is finite, $N$ is finite-dimensional with $\dim N \le \dim M$. Then $\dim N^* = \dim N$, and the injection $M \to N^*$ gives $\dim M \le \dim N$. So $\dim M = \dim N = \dim N^* = \dim M^*$, and an injective linear map between spaces of the same finite dimension is bijective (Volume 7, Chapter 2). $\square$

The injectivity of $M \to N^*$ says that $p(x, y) = 0$ for all $y$ forces $x = 0$. So over a field and in finite dimension, perfect means nondegenerate.

::: mathlib
`LinearMap.IsPerfPair.of_injective` · `Mathlib.LinearAlgebra.PerfectPairing.Basic`

The converse direction, with `FiniteDimensional K M` and the two injectivity hypotheses for `p` and `p.flip`. In the other direction, `IsPerfPair.nondegenerate` holds over each commutative ring, and `Module.finrank_of_isPerfPair` gives `finrank R M = finrank R N` for a finite free `M`. The instance `IsPerfPair.dualEval` states that the evaluation pairing $M \times M^* \to R$ is perfect for a reflexive module $M$.

<?decl LinearMap.IsPerfPair.of_injective?>
:::

<?decl LinearMap.IsPerfPair.nondegenerate?>

<?decl Module.finrank_of_isPerfPair?>

<?decl LinearMap.IsPerfPair.dualEval?>

### Examples

**Example (A Minkowski adjoint).** On $\mathbb{R}^2$ let $B$ have the matrix $A = \operatorname{diag}(1, -1)$. Then $A^{\mathsf{T}} = A = A^{-1}$, and the adjoint of $\Phi = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ is
$$\Psi = A \Phi^{\mathsf{T}} A = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \begin{pmatrix} a & c \\ b & d \end{pmatrix} \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} = \begin{pmatrix} a & -c \\ -b & d \end{pmatrix}.$$
So $\Phi$ is self-adjoint exactly when $c = -b$, not when $\Phi$ is symmetric.

**Example ($\mathrm{Sp}_2 = \mathrm{SL}_2$).** Let $\omega(x, y) = x_1 y_2 - x_2 y_1$ on $K^2$. Since $\omega(x, y)$ is the determinant of the matrix with the columns $x$ and $y$, $\omega(P x, P y) = \det P \cdot \omega(x, y)$ for each matrix $P$. So $P$ is an isometry of $\omega$ if and only if $\det P = 1$. In dimension 2 the symplectic group is the special linear group.

**Counterexample (Nondegenerate but not perfect).** On $\mathbb{Z}$ let $p(a, b) = 2 a b$. If $p(a, b) = 0$ for all $b$, then $a = 0$, so $p$ is nondegenerate. But $a \mapsto p(a, -)$ has image the forms $b \mapsto 2 a b$, which misses the identity form $b \mapsto b$. So $p$ is not perfect. Over a ring, nondegenerate is weaker than perfect.

**Counterexample (Infinite dimension).** On $V = K^{(\mathbb{N})}$, the sequences with finitely many nonzero terms, let $B(x, y) = \sum_i x_i y_i$. It is nondegenerate, since $B(x, e_j) = x_j$. The linear form $s(y) = \sum_i y_i$ is not $B(x, -)$ for any $x$: that would need $x_j = s(e_j) = 1$ for all $j$. So $V \to V^*$ is injective but not surjective, and the hypothesis of finite dimension in the theorem is necessary.

### The library around it

The pullbacks and basis lemmas are in `Mathlib.LinearAlgebra.BilinearForm.Hom`, the isometries in the two isometry files, the adjoints in the files of Section 1. Chapter 6 repeats the isometries for quadratic forms.

The file `Mathlib.LinearAlgebra.PerfectPairing.Restrict` restricts perfect pairings. Let $p : M \times N \to R$ be perfect, and let $M' \to M$ and $N' \to N$ be injective maps whose images are perfect complements for $p$ in the sense of `LinearMap.IsPerfectCompl`. Then the restricted pairing on $M' \times N'$ is perfect (`LinearMap.IsPerfPair.restrict`). The lemma `LinearMap.IsPerfPair.restrictScalars` restricts the scalars to a subring $S$ of $R$, under conditions of spanning and of values in $S$. Over fields the statement is simpler. Let $p$ be perfect over a field $L$, let $K \subseteq L$ be a subfield, and let $M'$ and $N'$ be $K$-subspaces that span $M$ and $N$ over $L$, with $p(x, y) \in K$ for $x \in M'$ and $y \in N'$. Then $\dim_K M' = \dim_L M$ (`LinearMap.finrank_eq_of_isPerfPair`), and `LinearMap.IsPerfPair.restrictScalars_of_field` gives the perfect $K$-pairing on these subspaces.

The file `Mathlib.LinearAlgebra.BilinearForm.DualLattice` defines the dual of a lattice. Let $B$ be a bilinear form on a vector space $M$ over a field $S$ that is an $R$-algebra, for example $R = \mathbb{Z}$ and $S = \mathbb{Q}$. For an $R$-submodule $N$, `LinearMap.BilinForm.dualSubmodule B N` is the $R$-submodule of the $x$ with $B(x, y) \in R$ for all $y \in N$ (`LinearMap.BilinForm.mem_dualSubmodule`). If $B$ is nondegenerate and $N$ is the $R$-span of a basis $b$, then the dual of $N$ is the $R$-span of the dual basis of $b$ (`LinearMap.BilinForm.dualSubmodule_span_of_basis`). For a symmetric $B$ the dual of the dual is $N$ again (`LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis`). For example, for $B(x, y) = 2 x y$ on $\mathbb{Q}$ the dual of $\mathbb{Z}$ is $\frac12 \mathbb{Z}$. The map `LinearMap.BilinForm.dualSubmoduleToDual` sends the dual of $N$ into the dual module of $N$, and it is injective when $B$ is nondegenerate and $N$ spans $M$ (`LinearMap.BilinForm.dualSubmoduleToDual_injective`).

### Exercises

1. (A) Show that the adjoint satisfies $(\varphi \chi)^* = \chi^* \varphi^*$ and $(a \varphi + \chi)^* = a \varphi^* + \chi^*$ for a nondegenerate form. Hint: use uniqueness.
2. (A) Show that equivalence of forms is an equivalence relation. Hint: compose and invert isometric isomorphisms.
3. (A) Show that the forms with matrices $\operatorname{diag}(1, 1)$ and $\operatorname{diag}(2, 2)$ on $\mathbb{Q}^2$ are equivalent. Hint: try $P = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$.
4. (B) Show that the forms with matrices $\operatorname{diag}(1, 1)$ and $\operatorname{diag}(1, 3)$ on $\mathbb{Q}^2$ are not equivalent. Hint: the discriminant of Section 1.
5. (B) For a nondegenerate $B$ with matrix $A$, find the matrix condition for $\varphi$ to be self-adjoint and for it to be skew-adjoint. Hint: use the formula for $\Psi$.
6. (C) Let $B$ be a nondegenerate form on $V$ of finite dimension. Show that $B$ is reflexive if and only if, for each map $\varphi$, the left and right adjoints of $\varphi$ agree. Hint: for the converse, define $\sigma$ by $B(y, x) = B(\sigma x, y)$, show that $\sigma$ commutes with every linear map, and deduce $B(y, x) = \varepsilon B(x, y)$ for a scalar $\varepsilon$.

### Notes and history

The orthogonal and symplectic groups are two families of the classical groups, the name of Hermann Weyl's 1939 book. Perfect pairings appear in the duality theorems of topology and number theory.

### Reference

<?reference?>
