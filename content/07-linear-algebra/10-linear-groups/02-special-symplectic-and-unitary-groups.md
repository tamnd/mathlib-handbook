---
title: Special linear, symplectic and unitary groups
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
  - Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
  - Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
  - Mathlib.LinearAlgebra.SpecialLinearGroup
  - Mathlib.LinearAlgebra.SymplecticGroup
  - Mathlib.LinearAlgebra.UnitaryGroup
explains:
  E2: [Matrix.SpecialLinearGroup, Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity, Matrix.SL2.transvection_induction, Matrix.ProjectiveSpecialLinearGroup, SpecialLinearGroup.SL2Z_generators, FixedDetMatrices.induction_on, SpecialLinearGroup, Matrix.symplecticGroup, SymplecticGroup.det_eq_one, Matrix.unitaryGroup]
  E1: auto
families: []
requires: [V03, V05, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Special linear, symplectic and unitary groups

### Overview

Section 1 defines the general linear group `GL n R`. This section treats the subgroups of it that are defined by one equation. The special linear group is defined by $\det A = 1$. The symplectic group is defined by $A J A^T = J$ for the standard alternating matrix $J$. The unitary group is defined by $A A^* = 1$, and the orthogonal group is the unitary group for the trivial star. For the special linear group, Mathlib has a matrix form and a form for modules. It also has the projective special linear group, the generation of $SL_2$ by transvections, and the generation of $SL_2(\mathbb{Z})$ by the two matrices $S$ and $T$.

### The library around it

#### The special linear group of matrices

**Definition (`Matrix.SpecialLinearGroup`).** For a finite type $n$ with decidable equality and a commutative ring $R$, `Matrix.SpecialLinearGroup n R` is the subtype of the matrices `A : Matrix n n R` with $\det A = 1$. The scoped notation `SL(m, R)` in the namespace MatrixGroups means `Matrix.SpecialLinearGroup (Fin m) R`.

The multiplication, the unit and the inverse are those of the matrices (`Matrix.SpecialLinearGroup.coe_mul`, `Matrix.SpecialLinearGroup.coe_one`, `Matrix.SpecialLinearGroup.coe_inv`). Because the determinant is $1$, the inverse is the adjugate. For size two, `Matrix.SpecialLinearGroup.SL2_inv_expl` gives the explicit formula $\begin{pmatrix} a & b \\ c & d \end{pmatrix}^{-1} = \begin{pmatrix} d & -b \\ -c & a \end{pmatrix}$. An element is made from a matrix and a proof of $\det A = 1$ with `Matrix.SpecialLinearGroup.mk`, and two elements are equal when their entries are equal (`Matrix.SpecialLinearGroup.ext`). For $2 \times 2$ matrices, `Matrix.SpecialLinearGroup.fin_two_induction` reduces a statement about all elements to a statement about `!![a, b; c, d]` with $a d - b c = 1$.

The constructions of Chapter 3 pass to the group: `Matrix.SpecialLinearGroup.map` for a ring homomorphism, `Matrix.SpecialLinearGroup.reindex` for an equivalence of index types, `Matrix.SpecialLinearGroup.transpose`, and the product forms `Matrix.SpecialLinearGroup.prodEquiv` and `Matrix.SpecialLinearGroup.piEquiv`. The map `Matrix.SpecialLinearGroup.toLin'` sends a matrix to its linear automorphism of $R^n$, and `Matrix.SpecialLinearGroup.toGL` of Section 1 is the inclusion into `GL n R`. When $|n|$ is even, $\det(-A) = \det A$, so the group has a negation (`Matrix.SpecialLinearGroup.coe_neg`).

#### The center

**Theorem (`Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity`).** The center of `Matrix.SpecialLinearGroup n R` is isomorphic to the group of the $k$th roots of unity in $R$, where $k = \max(|n|, 1)$.

*Proof sketch.* By the argument of Section 1, a central element commutes with each transvection, so it is a scalar matrix $r \cdot 1$ (`Matrix.SpecialLinearGroup.mem_center_iff`). Its determinant is $r^{|n|}$, so the condition $\det = 1$ says that $r$ is a root of unity of order $|n|$. When $n$ is empty, the group is trivial and the roots of unity of order $1$ are also trivial. $\square$

The version `Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'` uses an index $i$ of $n$ to read the scalar as the entry at $(i, i)$.

#### Generation by transvections

For $i \ne j$ and $c$ in $R$, `Matrix.SpecialLinearGroup.transvection` is the elementary matrix $1 + c E_{ij}$ of Chapter 4 Section 3, as an element of the special linear group. Over a field, the row reduction of Chapter 4 Section 3 writes each element as a product of transvections, a diagonal matrix of determinant $1$ and transvections (`Matrix.SpecialLinearGroup.exists_list_transvec_mul_diagonal_mul_list_transvec`).

**Theorem (`Matrix.SL2.transvection_induction`).** Let $F$ be a field and $P$ a property of the elements of `SL(2, F)`. If $P$ holds for each transvection and $P$ is stable under products, then $P$ holds for each element.

*Proof sketch.* By the decomposition above, it is sufficient to treat a diagonal matrix $\operatorname{diag}(a, a^{-1})$. The identity `Matrix.diag2_decompose` writes it as a product of six transvections. $\square$

Thus `SL(2, F)` is generated by its transvections. A transvection is also a commutator when the field has an element $a \ne 0$ with $a^2 \ne 1$ (`Matrix.transvection_mem_commutator`), and then the commutator subgroup of `SL(2, F)` is the full group (`Matrix.SL2.commutator_eq_top`). The condition fails only for the fields with two or three elements.

Over a commutative ring, the rows of an element of `SL(2, R)` are coprime pairs (`Matrix.SpecialLinearGroup.isCoprime_row`). Conversely, each coprime pair $(a, b)$ is a row of an element (`IsCoprime.exists_SL2_row`), and the same holds for columns (`IsCoprime.exists_SL2_col`).

#### The projective special linear group

**Definition (`Matrix.ProjectiveSpecialLinearGroup`).** `Matrix.ProjectiveSpecialLinearGroup n R` is the quotient of `Matrix.SpecialLinearGroup n R` by its center. The scoped notation is `PSL(m, R)`.

By the theorem on the center, `PSL(n, R)` is the quotient of $SL_n(R)$ by the scalar roots of unity of order $n$. For example, `PSL(2, ℤ)` is the quotient of `SL(2, ℤ)` by $\{1, -1\}$. Section 1 compares this group with the projective general linear group `Matrix.ProjGenLinGroup`.

#### The modular group and matrices of fixed determinant

The group `SL(2, ℤ)` is the modular group. It holds the two matrices `ModularGroup.S`, which is `!![0, -1; 1, 0]`, and `ModularGroup.T`, which is `!![1, 1; 0, 1]`. They satisfy $S^2 = -1$ (`ModularGroup.S_mul_S_eq`) and a relation with $T$ (`ModularGroup.T_S_rel`). The powers of $T$ have the formula `ModularGroup.coe_T_zpow`.

The module `Mathlib.LinearAlgebra.Matrix.FixedDetMatrices` proves that $S$ and $T$ generate the group. It works with the set `FixedDetMatrix n R m` of the matrices with determinant $m$, on which `Matrix.SpecialLinearGroup n R` acts by multiplication on the left. For $n = 2$ and $R = \mathbb{Z}$, the set `FixedDetMatrices.reps m` is the set of the upper triangular matrices $\begin{pmatrix} a & b \\ 0 & d \end{pmatrix}$ with $a > 0$ and $0 \le b < |d|$. These are the Hermite normal forms of the matrices of determinant $m$.

**Theorem (`FixedDetMatrices.induction_on`).** Let $m \ne 0$, and let $C$ be a property of the integer $2 \times 2$ matrices of determinant $m$. If $C$ holds for each element of `FixedDetMatrices.reps m`, and if $C(B)$ implies $C(S B)$ and $C(T B)$ for each $B$, then $C$ holds for each matrix of determinant $m$.

*Proof sketch.* This is the Euclidean algorithm on the first column. If the lower left entry $c$ is not zero, the step `FixedDetMatrices.reduceStep` multiplies by a power of $T$ and then by $S$. This replaces $c$ by the remainder of $a$ modulo $c$, so $|c|$ decreases. When $c = 0$, a power of $T$ and possibly $S^2 = -1$ put the matrix into the set of representatives (`FixedDetMatrices.reduce_mem_reps`). Each step is invertible, and the hypotheses on $S$ and $T$ also give the property for the inverse steps. $\square$

**Theorem (`SpecialLinearGroup.SL2Z_generators`).** The subgroup of `SL(2, ℤ)` generated by `ModularGroup.S` and `ModularGroup.T` is the full group.

*Proof sketch.* Apply the induction with $m = 1$ to the property "the matrix is in the subgroup". The only representative of determinant $1$ is the identity (`FixedDetMatrices.reps_one_id`). $\square$

The action of the modular group on the upper half plane and the modular forms are in Volume 12 Chapter 9.

#### The special linear group of a module

**Definition (`SpecialLinearGroup`).** For a commutative ring $R$ and an $R$-module $V$, `SpecialLinearGroup R V` is the subtype of the linear automorphisms $u : V \simeq V$ with $\det u = 1$.

The determinant of a linear equivalence is the one of Chapter 4 Section 1. When $V$ has no finite basis, this determinant is $1$ by convention, and then `SpecialLinearGroup R V` contains all the automorphisms. The definition uses linear equivalences and not linear maps, so that the inverse is available. The inclusion into the group of Section 1 is `SpecialLinearGroup.toGeneralLinearGroup`. A basis of $V$ indexed by $n$ gives the isomorphism `Matrix.SpecialLinearGroup.toLin_equiv` with the matrix group. A linear equivalence $V \simeq W$ gives `SpecialLinearGroup.congr_linearEquiv`, and for $V$ free and finite the module form has the maps `SpecialLinearGroup.dualMap` to the dual module of Chapter 6 and `SpecialLinearGroup.baseChange` to $S \otimes_R V$. The center is again a group of roots of unity (`SpecialLinearGroup.centerEquivRootsOfUnity`).

#### The symplectic group

**Definition (`Matrix.symplecticGroup`).** For a finite type $l$ and a commutative ring $R$, let `Matrix.J l R` be the block matrix $J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ indexed by `l ⊕ l`. Then `Matrix.symplecticGroup l R` is the submonoid of the matrices $A$ with $A J A^T = J$.

The membership lemma is `SymplecticGroup.mem_iff`. The matrix $J$ satisfies $J^2 = -1$ (`Matrix.J_squared`) and $J^T = -J$ (`Matrix.J_transpose`), and it is in the group (`SymplecticGroup.J_mem`). The submonoid is a group: each element has the inverse $-J A^T J$ (`SymplecticGroup.inv_eq_symplectic_inv`). The transpose of a symplectic matrix is symplectic (`SymplecticGroup.transpose_mem`).

**Theorem (`SymplecticGroup.det_eq_one`).** Over a commutative ring, each symplectic matrix has determinant $1$.

*Proof sketch.* The equation $A J A^T = J$ gives $\det(A)^2 \det J = \det J$, and $\det J$ is a unit (`Matrix.isUnit_det_J`), so $\det A$ is a unit (`SymplecticGroup.symplectic_det`). First let $R$ be a local ring, and write $A$ in blocks $\begin{pmatrix} P & Q \\ C & D \end{pmatrix}$. There is a symmetric matrix $X$ such that $P + X C$ is invertible. The product $\begin{pmatrix} 1 & X \\ 0 & 1 \end{pmatrix} A$ is symplectic, its upper left block is invertible, and the formula for the determinant of a block matrix of Chapter 5 Section 5 gives the determinant $1$. For a general ring, $\det A - 1$ is zero in the localization at each maximal ideal, so it is zero. $\square$

Thus the symplectic group is a subgroup of the special linear group. The matrix $J$ is the matrix of the standard alternating form of Chapter 6 Section 3.

#### Unitary and orthogonal groups

**Definition (`Matrix.unitaryGroup`).** For a commutative ring $\alpha$ with a star operation, `Matrix.unitaryGroup n α` is the submonoid of the matrices $A$ with $A A^* = 1$ and $A^* A = 1$, where $A^*$ is the conjugate transpose of Chapter 3 Section 7.

It is the submonoid `unitary` of Volume 3 for the matrix ring. The membership lemma `Matrix.mem_unitaryGroup_iff` needs only $A A^* = 1$, because a one-sided inverse of a square matrix is two-sided. In the group, the inverse is the star (`Matrix.star_eq_inv`). The determinant of a unitary matrix is a unitary element of $\alpha$ (`Matrix.det_of_mem_unitary`), so over $\mathbb{C}$ its absolute value is $1$. The map `Matrix.UnitaryGroup.embeddingGL` is the inclusion into `LinearMap.GeneralLinearGroup α (n → α)`. The special unitary group `Matrix.specialUnitaryGroup n α` adds the condition $\det A = 1$.

For a commutative ring $R$ with the trivial star, the unitary group is the orthogonal group `Matrix.orthogonalGroup n R`, with the condition $A A^T = 1$ (`Matrix.mem_orthogonalGroup_iff`). The special orthogonal group is `Matrix.specialOrthogonalGroup n R`. In size two, `Matrix.mem_specialOrthogonalGroup_fin_two_iff` says that its elements are the matrices `!![a, -b; b, a]` with $a^2 + b^2 = 1$, which are the rotations.

#### Common errors

1. An element `A : SL(2, ℤ)` is not a matrix. Use the coercion `↑A` for the matrix. The notations `SL(n, R)` and `PSL(n, R)` need `open MatrixGroups`.
2. `Matrix.symplecticGroup l R` contains matrices of size $2|l|$, indexed by `l ⊕ l`, and not by `Fin (2 * k)`. To work with `Fin (2 * k)`, reindex with an equivalence.
3. The lemmas about `Matrix.orthogonalGroup` use the local instance `starRingOfComm` for the trivial star. Over $\mathbb{C}$, `Matrix.unitaryGroup` uses the complex conjugation, so the orthogonal group and the unitary group are not the same.

### Exercises

1. (A) Show that `ModularGroup.S` has order $4$ in `SL(2, ℤ)`.
2. (A) Show that the matrix `!![0, -1; 1, 0]` over $\mathbb{R}$ is in `Matrix.specialOrthogonalGroup (Fin 2) ℝ`.
3. (B) Show that the center of `SL(2, ℚ)` has two elements and the center of `SL(3, ℚ)` has one element.
4. (B) Write the transvection `!![1, 0; 1, 1]` of `SL(2, ℤ)` as a product of powers of `ModularGroup.S` and `ModularGroup.T`.
5. (B) For $l$ with one element, show that `Matrix.symplecticGroup l R` and `SL(2, R)` contain the same $2 \times 2$ matrices, after reindexing.
6. (C) Show that `SL(2, ZMod 2)` has $6$ elements and that its commutator subgroup has $3$ elements, so `Matrix.SL2.commutator_eq_top` needs its hypothesis.

### Reference

<?reference?>
