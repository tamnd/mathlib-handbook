---
title: "Matrix rings: ideals, modules and actions"
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.Ideal
  - Mathlib.LinearAlgebra.Matrix.Action
  - Mathlib.LinearAlgebra.Matrix.Module
  - Mathlib.LinearAlgebra.Matrix.DualNumber
  - Mathlib.LinearAlgebra.Matrix.FiniteDimensional
  - Mathlib.LinearAlgebra.Matrix.CharP
  - Mathlib.LinearAlgebra.Matrix.Integer
  - Mathlib.LinearAlgebra.Matrix.BaseChange
explains:
  E2: [Ideal.matrix, TwoSidedIdeal.matrix, TwoSidedIdeal.equivMatrix, TwoSidedIdeal.jacobson_matrix, Matrix.smul_eq_mulVec, Matrix.Module.matrixModule, Matrix.dualNumberEquiv, Matrix.instCharP, Matrix.num, Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right]
  E1: auto
families: []
requires: [V04, V05, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Matrix rings: ideals, modules and actions

### Overview

The square matrices $\operatorname{Mat}_n(R)$ over a ring $R$ form a ring, and Section 4 shows that they form an $R$-algebra. This section collects the facts about this ring as a ring: its two-sided ideals, which correspond to the two-sided ideals of $R$; its natural modules, the column vectors $R^n$ and more generally $M^n$ for an $R$-module $M$; its characteristic; and some special entry rings, such as the dual numbers and the rationals.

These facts are the start of Morita theory, the study of rings with equivalent categories of modules. The ring $R$ and the ring $\operatorname{Mat}_n(R)$ are the basic example: they have the same lattice of two-sided ideals, and the functor $M \mapsto M^n$ is an equivalence of their module categories. The equivalence itself is in the volumes on rings and categories; this section gives the parts that live in the folder `Mathlib/LinearAlgebra/Matrix`.

### The library around it

#### Ideals of matrix rings

An ideal of $R$ gives the set of matrices with all entries in it.

**Definition (`Ideal.matrix`).** For an ideal $I$ of a semiring $R$ and a finite type $n$, `Ideal.matrix n I` is the left ideal of `Matrix n n R` of the matrices with all entries in $I$.

The membership rule is `Ideal.mem_matrix`. The construction is monotone (`Ideal.matrix_monotone`), strictly monotone when $n$ is not empty (`Ideal.matrix_strictMono_of_nonempty`), and it sends $\bot$ to $\bot$ and $\top$ to $\top$ (`Ideal.matrix_bot`, `Ideal.matrix_top`). In Mathlib an `Ideal` of a noncommutative ring is a left ideal, so for the correspondence of two-sided ideals the module uses the structure `TwoSidedIdeal`.

**Definition (`TwoSidedIdeal.matrix`).** For a two-sided ideal $I$ of a ring $R$, `TwoSidedIdeal.matrix n I` is the two-sided ideal of `Matrix n n R` of the matrices with all entries in $I$.

**Theorem (`TwoSidedIdeal.equivMatrix`).** For a nonempty finite type $n$, the map $I \mapsto \operatorname{Mat}_n(I)$ is a bijection from the two-sided ideals of $R$ to the two-sided ideals of `Matrix n n R`.

*Proof sketch.* The inverse sends a two-sided ideal $J$ of matrices to the set of entries of the matrices in $J$ (`TwoSidedIdeal.coe_equivMatrix_symm_apply`). This set is an ideal of $R$. For the composition in one order: if $M \in J$, then the product $E_{ki} M E_{jl}$ with the matrix units of Section 5 is the matrix with the single entry $M_{ij}$ at $(k, l)$, and it is in $J$. A sum of such matrices gives each matrix with entries in the ideal of entries, so $J$ is $\operatorname{Mat}_n$ of this ideal. The other order is clear. $\square$

The order isomorphism is `TwoSidedIdeal.orderIsoMatrix`. Mathlib proves the result first for ring congruences, with `RingCon.matrix` and its inverse `RingCon.ofMatrix`, and transfers it to ideals; the relation between the two is `TwoSidedIdeal.matrix_ringCon`. A consequence is that $\operatorname{Mat}_n(K)$ is a simple ring for each field $K$, because $K$ has only the two ideals $0$ and $K$.

The Jacobson radical of an ideal $I$, the intersection of the maximal left ideals that contain $I$, also behaves well.

**Theorem (`TwoSidedIdeal.jacobson_matrix`).** For a two-sided ideal $I$ of $R$, the Jacobson radical of $\operatorname{Mat}_n(I)$ is $\operatorname{Mat}_n$ of the Jacobson radical of $I$.

The special case `TwoSidedIdeal.matrix_jacobson_bot` says that the Jacobson radical of $\operatorname{Mat}_n(R)$ is $\operatorname{Mat}_n(J(R))$. For left ideals, there is only the inclusion `Ideal.matrix_jacobson_le`, and `Ideal.single_mem_jacobson_matrix` says that a matrix unit with an entry in the radical is in the radical.

#### Matrices acting on vectors

A square matrix acts on column vectors by the product `Matrix.mulVec`. The module `Mathlib.LinearAlgebra.Matrix.Action` makes this an action.

**Theorem (`Matrix.smul_eq_mulVec`).** With the instance `Matrix.instModuleForall`, the vectors $n \to R$ are a module over `Matrix n n R`, and `A • v = A.mulVec v`.

The opposite ring acts by the product on the other side: `Matrix.op_smul_eq_vecMul` says that $A^{\mathrm{op}}$ acts on a row vector $v$ by $v A$. The compatibility instances `Matrix.instIsScalarTowerForall` and `Matrix.instSMulCommClassForall` relate the action to the action of the scalars. Two matrices are equal when they act in the same way on all vectors: `Matrix.ext_iff_smul`.

For an $R$-module $M$, the same formula gives an action on $M^n$.

**Definition (`Matrix.Module.matrixModule`).** For a ring $R$ and an $R$-module $M$, the scoped instance `Matrix.Module.matrixModule` makes $n \to M$ a module over `Matrix n n R`, with $(N v)_i = \sum_j N_{ij} v_j$.

The instance is scoped, in the namespace Matrix.Module, because for $M = R$ or $M$ = `Matrix n n R` it gives a second action on a type that already has one. The formula is `Matrix.Module.smul_apply`, and the lemmas `Matrix.Module.single_smul`, `Matrix.Module.scalar_smul` and `Matrix.Module.diagonal_const_smul` compute the action of matrix units and of scalar matrices. An $R$-linear map $f : M \to N$ gives the map `LinearMap.mapMatrixModule ι f` from $M^n$ to $N^n$, linear over the matrices; with `LinearMap.mapMatrixModule_id` and `LinearMap.mapMatrixModule_comp` this is a functor from $R$-modules to $\operatorname{Mat}_n(R)$-modules, the functor of Morita theory.

#### Special rings of entries

The ring of dual numbers $R[\varepsilon] = R \oplus R \varepsilon$ with $\varepsilon^2 = 0$ is the trivial square zero extension of Volume 6. A matrix of dual numbers splits into two matrices.

**Definition (`Matrix.dualNumberEquiv`).** For a commutative semiring $R$, `Matrix.dualNumberEquiv` is the $R$-algebra isomorphism from the matrices over $R[\varepsilon]$ to the dual numbers over the matrices, which sends $A + B \varepsilon$ to the pair $(A, B)$.

The lemmas `Matrix.dualNumberEquiv_apply` and `Matrix.dualNumberEquiv_symm_apply` give the two directions. The isomorphism is used to compute derivatives of matrix functions, since $f(A + B \varepsilon) = f(A) + f'(A)(B) \varepsilon$ for a polynomial $f$.

The characteristic of the matrix ring is that of the entries.

**Theorem (`Matrix.instCharP`).** For a nonempty type $n$, if $R$ has characteristic $p$, then `Matrix n n R` has characteristic $p$.

*Proof.* The natural number $k$ in the matrix ring is the scalar matrix with the entry $k$ on the diagonal. It is zero if and only if $k = 0$ in $R$, since the diagonal has at least one entry. $\square$

The variants are `Matrix.instCharZero` and `Matrix.instExpChar`. The module `Mathlib.LinearAlgebra.Matrix.FiniteDimensional` gives the instance `Matrix.finiteDimensional`: the matrices over a field are a finite dimensional vector space. It also gives `LinearMap.finiteDimensional`, for the space of linear maps between two finite dimensional spaces.

A rational matrix is an integer matrix divided by a common denominator.

**Definition (`Matrix.num` and `Matrix.den`).** For a rational matrix $A$, `Matrix.den A` is the least common multiple of the denominators of the entries, and `Matrix.num A` is the integer matrix with $A = \frac{1}{d} N$.

The main identity is `Matrix.inv_denom_smul_num`. The lemma `Matrix.den_dvd_iff` says that $d$ divides a natural number $r$ if and only if each denominator divides $r$, and `Matrix.den_ne_zero` that the denominator is not zero. The casts of integer matrices have denominator $1$ (`Matrix.den_map_intCast`), and the casts respect products (`Matrix.map_mul_intCast`, `Matrix.map_mul_ratCast`). These are used to reduce a statement about rational matrices to a statement about integer matrices, for example in the theory of lattices of Chapter 9.

#### Inverses over a subfield

**Theorem (`Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right`).** Let $K$ be a subfield of a field $L$, and let $A$ and $B$ be matrices over $L$ of square shape, with $A B = 1$. If all entries of $A$ are in $K$, then all entries of $B$ are in $K$.

*Proof sketch.* View $A$ as a matrix $A'$ over $K$. Its determinant is the determinant of $A$, which is not zero since $A B = 1$. So $A'$ has an inverse over $K$, and the image of this inverse in $L$ is an inverse of $A$. A one-sided inverse of a square matrix over a field is the inverse, so $B$ is this image. $\square$

The left version is `Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left`. The shapes need only an equivalence between the row type and the column type, not equal types.

#### Common errors

1. `Ideal.matrix n I` is a left ideal. For the bijection with the ideals of $R$, use `TwoSidedIdeal.matrix` and `TwoSidedIdeal.equivMatrix`.
2. The action of matrices on $M^n$ is a scoped instance. Without `open Matrix.Module`, the expression `N • v` for $v : n \to M$ does not find it.
3. `Matrix.instCharP` needs a nonempty index type: the matrices over the empty type form the zero ring, of characteristic $1$.

### Exercises

1. (A) Show that the matrices over $\mathbb{Z}$ with all entries even form a two-sided ideal of `Matrix (Fin 2) (Fin 2) ℤ`, with `TwoSidedIdeal.mem_matrix`.
2. (A) Compute `Matrix.num` and `Matrix.den` of `!![1/2, 1/3; 0, 1]`.
3. (B) Prove that $\operatorname{Mat}_2(\mathbb{Q})$ has no two-sided ideals other than $0$ and the whole ring.
4. (B) Show that the left ideal of $2 \times 2$ matrices over a field with first column zero is not a two-sided ideal.
5. (B) Prove that for a nonempty $n$ the matrix ring over $\mathbb{Z}/p\mathbb{Z}$ has characteristic $p$, and that for an empty $n$ the matrix ring is the zero ring.
6. (C) Let $A$ be an invertible matrix with rational entries, viewed over $\mathbb{R}$. Prove that $A^{-1}$ has rational entries, with `Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right`.

### Reference

<?reference?>
