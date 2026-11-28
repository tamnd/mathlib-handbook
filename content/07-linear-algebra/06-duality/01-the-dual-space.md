---
title: The dual space and the dual basis
kind: theory
modules:
  - Mathlib.LinearAlgebra.Dual.Defs
  - Mathlib.LinearAlgebra.Dual.Basis
  - Mathlib.LinearAlgebra.Dual.BaseChange
explains:
  E3: [Module.Dual, Module.Basis.dualBasis, Module.Dual.eval]
  E2: [Module.Basis.dualBasis_apply_self, Module.Basis.dualBasis_repr, Module.Basis.coe_dualBasis, Module.Basis.coord, Module.Basis.toDual, Module.Basis.toDualEquiv, Module.Dual.eval_apply, Module.evalEquiv, Module.IsReflexive, Module.Basis.sum_dual_apply_smul_coord]
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

## The dual space and the dual basis

### Overview

A linear functional on a vector space $V$ over $K$ is a linear map $V \to K$. Examples are the coordinate functions in a basis, the trace of a matrix, the evaluation of a polynomial at a point, and the integral of a continuous function. The functionals form a vector space $V^*$, the dual space. This section constructs the dual basis of a basis, proves $\dim V^* = \dim V$ in finite dimension, shows that the equality fails in infinite dimension, and proves that the evaluation $V \to V^{**}$ is an isomorphism in finite dimension.

### Definitions

**Definition (Dual space).** For a module $M$ over a commutative ring $R$, the dual $M^* = \operatorname{Hom}_R(M, R)$ is the module of the linear maps $M \to R$, with the pointwise operations.

::: mathlib
`Module.Dual` · `Mathlib.LinearAlgebra.Dual.Defs`

The dual module `Module.Dual R M`, an abbreviation for `M →ₗ[R] R`. So each lemma on linear maps applies to a functional.

<?decl Module.Dual?>
:::

**Definition (Coordinate functionals).** Let $b = (b_i)_{i \in I}$ be a basis of $M$. Each $x \in M$ is a unique combination $x = \sum_i c_i b_i$. The coordinate functional $b_i^*$ sends $x$ to $c_i$. It is linear and satisfies $b_i^*(b_j) = \delta_{ij}$, which is $1$ if $i = j$ and $0$ otherwise.

::: mathlib
`Module.Basis.coord` · `Mathlib.LinearAlgebra.Basis.Defs`

The coordinate functional `b.coord i : M →ₗ[R] R`, defined from the coordinates `b.repr x i`. It exists for each basis, finite or not.

<?decl Module.Basis.coord?>
:::

**Definition (Dual basis).** If $I$ is finite, the family $(b_i^*)_{i \in I}$ is a basis of $M^*$, by the theorem below. It is the dual basis of $b$.

::: mathlib
`Module.Basis.dualBasis` · `Mathlib.LinearAlgebra.Dual.Basis`

The dual basis `b.dualBasis : Basis ι R (Dual R M)` of a basis with a finite index type.

<?decl Module.Basis.dualBasis?>
:::

::: mathlib
`Module.Basis.coe_dualBasis` · `Mathlib.LinearAlgebra.Dual.Basis`

The elements of the dual basis are the coordinate functionals: `⇑b.dualBasis = b.coord`.

<?decl Module.Basis.coe_dualBasis?>
:::

::: mathlib
`Module.Basis.dualBasis_apply_self` · `Mathlib.LinearAlgebra.Dual.Basis`

The defining property `b.dualBasis i (b j) = if j = i then 1 else 0`.

<?decl Module.Basis.dualBasis_apply_self?>
:::

**Definition (Evaluation).** The evaluation map $\operatorname{ev} : M \to M^{**}$ sends $x$ to the functional $\varphi \mapsto \varphi(x)$ on $M^*$. It is linear, and it needs no choice of a basis.

::: mathlib
`Module.Dual.eval` · `Mathlib.LinearAlgebra.Dual.Defs`

The evaluation `Dual.eval R M : M →ₗ[R] Dual R (Dual R M)`.

<?decl Module.Dual.eval?>
:::

::: mathlib
`Module.Dual.eval_apply` · `Mathlib.LinearAlgebra.Dual.Defs`

The formula `Dual.eval R M v a = a v`.

<?decl Module.Dual.eval_apply?>
:::

### Theorems and proofs

**Theorem (Dual basis).** Let $b_1, \dots, b_n$ be a finite basis of $M$. Then $b_1^*, \dots, b_n^*$ is a basis of $M^*$, and each $\varphi \in M^*$ has the expansion $\varphi = \sum_i \varphi(b_i) \, b_i^*$. In particular, $M^*$ is free of rank $n$, and $\dim V^* = \dim V$ for a space of finite dimension.

*Proof.* Spanning: both sides of the expansion are linear and agree on each $b_j$, since $\sum_i \varphi(b_i) b_i^*(b_j) = \varphi(b_j)$. A linear map is determined by its values on a basis, so they are equal. Independence: if $\sum_i c_i b_i^* = 0$, apply it to $b_j$ to get $c_j = 0$. $\square$

::: mathlib
`Module.Basis.sum_dual_apply_smul_coord` · `Mathlib.LinearAlgebra.Dual.Basis`

The expansion `∑ x, f (b x) • b.coord x = f` of a functional in the coordinate functionals.

<?decl Module.Basis.sum_dual_apply_smul_coord?>
:::

::: mathlib
`Module.Basis.dualBasis_repr` · `Mathlib.LinearAlgebra.Dual.Basis`

The coordinates of a functional in the dual basis: `b.dualBasis.repr l i = l (b i)`.

<?decl Module.Basis.dualBasis_repr?>
:::

**Theorem (Isomorphism with the dual).** With a finite basis $b$, the linear map $M \to M^*$ that sends $b_i$ to $b_i^*$ is an isomorphism.

*Proof.* It sends a basis to a basis. $\square$

This isomorphism depends on the basis. For $V = K$ with the basis $(1)$, it sends $1$ to the identity functional. With the basis $(2)$ over $\mathbb{Q}$, it sends $2$ to the functional $x \mapsto x/2$, so it sends $1$ to $x \mapsto x/4$. The two isomorphisms differ.

::: mathlib
`Module.Basis.toDual` · `Mathlib.LinearAlgebra.Dual.Basis`

The map `b.toDual : M →ₗ[R] Dual R M` that sends `b i` to `b.coord i`. It is defined for each basis, and it is injective.

<?decl Module.Basis.toDual?>
:::

::: mathlib
`Module.Basis.toDualEquiv` · `Mathlib.LinearAlgebra.Dual.Basis`

For a finite basis, `b.toDual` as a linear equivalence `M ≃ₗ[R] Dual R M`.

<?decl Module.Basis.toDualEquiv?>
:::

**Theorem (Double dual).** For a space $V$ of finite dimension, the evaluation $V \to V^{**}$ is an isomorphism.

*Proof.* Injective: let $x \neq 0$. Extend $x$ to a basis $x = b_1, b_2, \dots, b_n$ by Chapter 2. Then $b_1^*(x) = 1$, so $\operatorname{ev}(x) \neq 0$. By the theorem on the dual basis applied twice, $\dim V^{**} = \dim V^* = \dim V$. An injective linear map between spaces of the same finite dimension is an isomorphism, by rank-nullity. $\square$

The proof of injectivity works in each dimension. Only the surjectivity needs finite dimension.

::: mathlib
`Module.IsReflexive` · `Mathlib.LinearAlgebra.Dual.Defs`

The class of the modules for which `Dual.eval` is bijective. Each free module of finite rank has an instance, and so each space of finite dimension.

<?decl Module.IsReflexive?>
:::

::: mathlib
`Module.evalEquiv` · `Mathlib.LinearAlgebra.Dual.Defs`

For a reflexive module, the evaluation as a linear equivalence `M ≃ₗ[R] Dual R (Dual R M)`. It is canonical: no basis enters its definition.

<?decl Module.evalEquiv?>
:::

### Examples

**Example (A dual basis in $\mathbb{Q}^2$).** Let $b_1 = (1, 1)$ and $b_2 = (1, -1)$. A vector $(x, y)$ is $\tfrac{x + y}{2} b_1 + \tfrac{x - y}{2} b_2$. So $b_1^*(x, y) = \tfrac{x + y}{2}$ and $b_2^*(x, y) = \tfrac{x - y}{2}$. Check: $b_1^*(b_1) = 1$, $b_1^*(b_2) = 0$, $b_2^*(b_1) = 0$, $b_2^*(b_2) = 1$. The first coordinate functional of the standard basis, $e_1^*(x, y) = x$, is not $b_1^*$, although $b_1$ has the first coordinate $1$: the functional $b_1^*$ depends on the whole basis, not only on $b_1$.

**Example (A dual basis by matrix inversion).** In $K^n$, write the basis vectors $b_j$ as the columns of an invertible matrix $P$. A functional is a row vector $\varphi$, with $\varphi(x) = \varphi x$. The conditions $b_i^*(b_j) = \delta_{ij}$ say that the rows of the matrix $Q$ with the rows $b_i^*$ satisfy $Q P = I$. So the dual basis is formed by the rows of $P^{-1}$. For the last example, $P = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$ and $P^{-1} = \tfrac{1}{2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$, whose rows are $b_1^*$ and $b_2^*$.

**Example (Evaluation at points).** Let $V$ be the space of the polynomials of degree at most $2$ over $\mathbb{Q}$, and $\operatorname{ev}_a(p) = p(a)$. The functionals $\operatorname{ev}_0, \operatorname{ev}_1, \operatorname{ev}_2$ are a basis of $V^*$. They are the dual basis of the Lagrange polynomials $L_0 = \tfrac{(X - 1)(X - 2)}{2}$, $L_1 = -X(X - 2)$, $L_2 = \tfrac{X(X - 1)}{2}$, since $L_i(j) = \delta_{ij}$. The expansion of a functional reads $\varphi = \varphi(L_0) \operatorname{ev}_0 + \varphi(L_1) \operatorname{ev}_1 + \varphi(L_2) \operatorname{ev}_2$. For $\varphi(p) = \int_0^2 p$: $\varphi(L_0) = \tfrac13$, $\varphi(L_1) = \tfrac43$, $\varphi(L_2) = \tfrac13$, which is the rule of Simpson, exact for the degree at most $2$.

**Counterexample (Infinite dimension).** Let $V = K[X]$, with the basis $1, X, X^2, \dots$. A functional is determined by its values on this basis, and the values can be arbitrary. So $V^* \cong K^{\mathbb{N}}$, the space of all sequences. The coordinate functionals $e_k^*$ span only the sequences with finitely many nonzero terms, so they are not a basis of $V^*$. For $K = \mathbb{Q}$, $V$ is countable and $V^*$ is not, so $V \not\cong V^*$. Also $\operatorname{ev} : V \to V^{**}$ is not surjective.

### The library around it

The definitions are in `Mathlib.LinearAlgebra.Dual.Defs`, and the dual bases in `Mathlib.LinearAlgebra.Dual.Basis`. The file `Mathlib.LinearAlgebra.Dual.Lemmas` has the results that need a field, such as `Subspace.dual_finrank_eq`. The general notion of a dual pair of bases is `Module.DualBases`. For the matrices of $K^n$, `dotProductEquiv` identifies $K^n$ with its dual by the dot product.

The file `Mathlib.LinearAlgebra.Dual.BaseChange` compares the dual with a change of the ring of scalars. For an $R$-algebra $A$, a linear form $f$ on $V$ gives the linear form `Module.Dual.baseChange A f` on $A \otimes_R V$, with $a \otimes v \mapsto f(v) a$ (`Module.Dual.baseChange_apply_tmul`). When $V$ is free of finite rank, these forms span the dual: `IsBaseChange.toDualBaseChange` is the linear equivalence $A \otimes_R V^* \simeq (A \otimes_R V)^*$, and `IsBaseChange.dual` says that the dual of a base change is the base change of the dual. A linear equivalence $V \simeq W$ gives the equivalence `Module.Dual.congr` of the duals. The tensor products are in Volume 8.

Common errors of a learner:

- `Module.Dual R M` is `M →ₗ[R] R`, so a functional is applied as a function: `φ x`.
- `b.toDual` depends on `b`. For a canonical statement, use `Dual.eval` or the dual map of the next section.

### Exercises

1. (A) Find the dual basis of $(1, 0, 0)$, $(1, 1, 0)$, $(1, 1, 1)$ in $\mathbb{Q}^3$. Hint: invert the matrix with these columns.
2. (A) Show that the trace is a nonzero functional on $M_n(K)$, and find its expansion in the dual basis of the matrix units $E_{ij}$.
3. (A) Show that for $x \neq y$ in a vector space there is a functional $\varphi$ with $\varphi(x) \neq \varphi(y)$.
4. (B) Let $a_0, \dots, a_n$ be distinct in $K$. Show that $\operatorname{ev}_{a_0}, \dots, \operatorname{ev}_{a_n}$ are a basis of the dual of the polynomials of degree at most $n$. Hint: the Vandermonde determinant of Chapter 4.
5. (B) Show that the double dual isomorphism commutes with linear maps: $f^{**} \circ \operatorname{ev}_V = \operatorname{ev}_W \circ f$, with the dual maps of the next section.
6. (C) Show that $\mathbb{Z}/2$ is a $\mathbb{Z}$-module with dual $0$. Conclude that the evaluation map need not be injective over a ring.

### Notes and history

Dual spaces arose in the projective geometry of the nineteenth century, where the points and the hyperplanes are dual. In analysis, the dual of a normed space became central with the work of Riesz, Hahn and Banach in the 1910s and 1920s. The double dual and its canonical isomorphism were the motivating example of a natural transformation for Eilenberg and Mac Lane in 1945: the isomorphism $V \cong V^*$ depends on a basis, and the isomorphism $V \cong V^{**}$ does not.

The class `Module.IsReflexive` records the isomorphism with the double dual without a fixed basis.

### Reference

<?reference?>
