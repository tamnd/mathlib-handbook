---
title: Cartan matrices and their realisations
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.Cartan
  - Mathlib.LinearAlgebra.Matrix.Cartan.Basic
  - Mathlib.LinearAlgebra.Matrix.Cartan.Realisation
  - Mathlib.LinearAlgebra.Matrix.Symmetrizable
explains:
  E2: [CartanMatrix.A, CartanMatrix.E, CartanMatrix.E_det, Matrix.IsSimplyLaced, Matrix.IsGeneralizedCartan, Matrix.IsFiniteCartan, Matrix.IsFiniteCartan.det_pos, Matrix.IsSymmetrizable, CartanMatrix.Realisation, Matrix.IsFiniteCartan.toRootPairing]
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

## Cartan matrices and their realisations

### Overview

A Cartan matrix is a square integer matrix with $2$ on the diagonal and nonpositive entries off the diagonal, with a condition of positivity. The Cartan matrices of finite type classify the simple Lie algebras over $\mathbb{C}$ and the reduced irreducible root systems: there are the four families $A_n$, $B_n$, $C_n$, $D_n$ and the five exceptional matrices $E_6$, $E_7$, $E_8$, $F_4$, $G_2$.

This section describes the matrices themselves and the linear algebra around them. It gives the explicit matrices of Mathlib, the predicates of generalized and finite type, the symmetrizable matrices, and the realisation of a Cartan matrix by vectors and covectors in a perfect pairing. A realisation is the bridge from a matrix to a root system. The theory of root systems, with the Cartan matrix of a base, is in Volume 29 Chapter 7.

The module `Mathlib.LinearAlgebra.Matrix.Cartan` is a deprecated module that only imports `Mathlib.LinearAlgebra.Matrix.Cartan.Basic`.

### The library around it

#### The explicit Cartan matrices

All the matrices are integer matrices indexed by `Fin n`.

**Definition (`CartanMatrix.A`).** For a natural number $n$, `CartanMatrix.A n` is the $n \times n$ matrix with $2$ on the diagonal, $-1$ at the positions $(i, i + 1)$ and $(i + 1, i)$, and $0$ elsewhere.

It is the Cartan matrix of type $A_{n - 1}$, the type of the Lie algebra $\mathfrak{sl}_n$. The small cases are `CartanMatrix.A_one`, `CartanMatrix.A_two` and `CartanMatrix.A_three`, for example $A_2$ = `!![2, -1; -1, 2]`. The matrix is symmetric (`CartanMatrix.A_isSymm`), its diagonal is $2$ (`CartanMatrix.A_diag`), and its entries off the diagonal are nonpositive (`CartanMatrix.A_apply_le_zero_of_ne`).

The other classical families are `CartanMatrix.B` and `CartanMatrix.C`, of the types $B_n$ and $C_n$ of $\mathfrak{so}_{2n+1}$ and $\mathfrak{sp}_{2n}$, and `CartanMatrix.D`, of type $D_n$ of $\mathfrak{so}_{2n}$. The matrices $B_n$ and $C_n$ have one entry $-2$, and they are transposes of each other (`CartanMatrix.B_transpose`, `CartanMatrix.C_transpose`). The matrix $D_n$ is symmetric (`CartanMatrix.D_isSymm`). Mathlib orders the indices of $D_n$ so that the branch of the Dynkin diagram is at the first three nodes; see `CartanMatrix.D_four`. The lemma `CartanMatrix.D_three'` says that $D_3$ is $A_3$ after a permutation of the indices, the isomorphism $\mathfrak{so}_6 \cong \mathfrak{sl}_4$.

**Definition (`CartanMatrix.E`).** For a natural number $n$, `CartanMatrix.E n` is the $n \times n$ matrix of the Dynkin diagram with a chain of nodes $0, 2, 3, \dots, n - 1$ and one more node $1$ joined to node $3$.

The cases $n = 6, 7, 8$ are the exceptional matrices, written out in `CartanMatrix.E_six_eq`, `CartanMatrix.E_seven_eq` and `CartanMatrix.E_eight_eq`. For other values of $n$ the matrix is still defined, but it is not of finite type when $n \ge 9$. The other exceptional matrices are `CartanMatrix.F₄` and `CartanMatrix.G₂` = `!![2, -3; -1, 2]`; Mathlib uses the transpose of the $G_2$ matrix of Bourbaki.

**Theorem (`CartanMatrix.E_det`).** For $n \ge 3$, the determinant of `CartanMatrix.E n` is $9 - n$.

*Proof sketch.* Expand the determinant along the last row and the last column, where the matrix has the entries $2$ and $-1$. This gives the recursion $\det E_{n+2} = 2 \det E_{n+1} - \det E_n$ for $n \ge 4$ (`CartanMatrix.det_E_add_two`). A sequence with this recursion is an arithmetic progression. The values for $n = 3, 4$ are computed directly, and they are $6$ and $5$. $\square$

So $\det E_6 = 3$, $\det E_7 = 2$ and $\det E_8 = 1$ (`CartanMatrix.E₈_det`), and $\det E_9 = 0$, which shows that $E_9$ is not of finite type. The determinants of $F_4$ and $G_2$ are $1$ (`CartanMatrix.F₄_det`, `CartanMatrix.G₂_det`). For a root system, this determinant is the index of the root lattice in the weight lattice.

**Definition (`Matrix.IsSimplyLaced`).** An integer matrix is simply laced when each entry off the diagonal is $0$ or $-1$.

The types $A$, $D$ and $E$ are simply laced (`CartanMatrix.isSimplyLaced_A`, `CartanMatrix.isSimplyLaced_D`, `CartanMatrix.isSimplyLaced_E`), and $F_4$ and $G_2$ are not (`CartanMatrix.not_isSimplyLaced_F₄`, `CartanMatrix.not_isSimplyLaced_G₂`). The predicate is decidable for a finite index type, so the decide tactic checks it. The exceptional matrices are indecomposable in the sense of `Matrix.IsIndecomposable`: no reindexing gives a block triangular form (`CartanMatrix.isIndecomposable_E_eight`, `CartanMatrix.isIndecomposable_G₂`).

#### Generalized and finite Cartan matrices

**Definition (`Matrix.IsGeneralizedCartan`).** An integer square matrix $M$ is a generalized Cartan matrix when $M_{ii} = 2$ for all $i$, $M_{ij} \le 0$ for $i \ne j$, and $M_{ij} = 0$ if and only if $M_{ji} = 0$.

The fields are `Matrix.IsGeneralizedCartan.diag`, `Matrix.IsGeneralizedCartan.offDiag_nonpos` and `Matrix.IsGeneralizedCartan.zero_comm`. The generalized Cartan matrices are the matrices of the Kac and Moody Lie algebras, which can have infinite dimension.

**Definition (`Matrix.IsFiniteCartan`).** A generalized Cartan matrix $M$ indexed by a finite type is of finite type when there are integers $d_i > 0$ with $x \cdot (\operatorname{diag}(d) M x) > 0$ for each integer vector $x \ne 0$.

The constructor `Matrix.IsFiniteCartan.mk_of_exists_posDef` accepts instead the condition that $\operatorname{diag}(d) M$ is positive definite in the sense of `Matrix.PosDef` of Chapter 5 Section 5, and `Matrix.IsFiniteCartan.exists_posDef` gives this form back. Then $\operatorname{diag}(d) M$ is symmetric, so a finite Cartan matrix is symmetrizable with positive weights (`Matrix.IsFiniteCartan.isPosSymmetrizable`). The predicate is kept by the transpose (`Matrix.IsFiniteCartan.transpose_iff`) and by principal submatrices (`Matrix.IsFiniteCartan.submatrix`).

**Theorem (`Matrix.IsFiniteCartan.det_pos`).** The determinant of a finite Cartan matrix is positive.

*Proof.* The matrix $\operatorname{diag}(d) M$ is positive definite, so its determinant is positive by `Matrix.PosDef.det_pos`. This determinant is $\prod_i d_i \cdot \det M$, and $\prod_i d_i > 0$. So $\det M > 0$. $\square$

So a finite Cartan matrix is invertible over each field of characteristic zero (`Matrix.IsFiniteCartan.isUnit_map`). Other consequences are `Matrix.IsFiniteCartan.exists_pos_and_mulVec_pos`, a vector $u$ with positive entries such that $M u$ has positive entries, and `Matrix.IsFiniteCartan.exists_apply_ne_zero_and`, which finds a row with at most one nonzero entry off the diagonal; this is an end node of the Dynkin diagram, and it is the start of the classification by induction. The bound on eigenvalues of Chapter 5 Section 5 applies: each eigenvalue of a finite Cartan matrix, viewed as a real matrix, is less than $4$.

#### Symmetrizable matrices

**Definition (`Matrix.IsSymmetrizable`).** A square matrix $M$ over a monoid with zero is symmetrizable when there are elements $d_i$ that are not zero divisors with $d_i M_{ij} = d_j M_{ji}$ for all $i$ and $j$.

The lemma `Matrix.isSymmetrizable_iff` says that this means that $\operatorname{diag}(d) M$ is symmetric for such a $d$, and `Matrix.isSymmetrizable_iff'` uses an invertible diagonal matrix instead. In a symmetrizable matrix, $M_{ij} = 0$ if and only if $M_{ji} = 0$ (`Matrix.IsSymmetrizable.apply_eq_zero_iff`). A symmetric matrix is symmetrizable (`Matrix.IsSymm.isSymmetrizable`), and the predicate is kept by the transpose, by principal submatrices and by the addition of a diagonal matrix (`Matrix.isSymmetrizable_add_diagonal_iff`).

The variant `Matrix.IsPosSymmetrizable` asks for $d_i > 0$, and `Matrix.isPosSymmetrizable_iff` is its form with a diagonal matrix. To prove it, `Matrix.IsPosSymmetrizable.mk_of_forall_ne` extends a positive symmetrizer from the indices other than $k$ to all indices. Over a field, a symmetrizable matrix $M$ is similar to the symmetric matrix $D^{1/2} M D^{-1/2}$ when the $d_i$ have square roots, which is the reason for the name.

#### Realisations

A realisation of a Cartan matrix is a family of simple roots and simple coroots with the given pairings.

**Definition (`CartanMatrix.Realisation`).** For a finite type $n$, a commutative ring $R$ and $R$-modules $M$ and $N$, a realisation consists of vectors $r_i \in M$, covectors $c_j \in N$, a finite Cartan matrix $A$ and a perfect pairing $\langle \cdot, \cdot \rangle : M \times N \to R$, with $\langle r_i, c_j \rangle = A_{ij}$ for all $i$ and $j$.

The fields are `CartanMatrix.Realisation.sRoot`, `CartanMatrix.Realisation.sCoroot`, `CartanMatrix.Realisation.matrix` and `CartanMatrix.Realisation.pairing`. Each root gives a reflection $s_i(x) = x - \langle x, c_i \rangle r_i$ of $M$ (`CartanMatrix.Realisation.reflection_apply`), and each coroot a reflection of $N$. The pairs of these reflections generate the Weyl group `CartanMatrix.Realisation.weylGroup`, which keeps the pairing (`CartanMatrix.Realisation.pairing_apply_apply_of_mem_weyl`). The roots of the realisation are the images of the simple roots under the Weyl group, `CartanMatrix.Realisation.idx`. Over a domain of characteristic zero, the Weyl group and the set of roots are finite, and the simple roots are linearly independent (`CartanMatrix.Realisation.lin_ind_sRoot`).

The main construction gives a root pairing in the sense of Volume 29: `CartanMatrix.Realisation.toRootPairing` is a reduced crystallographic root pairing, and `CartanMatrix.Realisation.rootPairingBase` is a base with Cartan matrix $A$ (`CartanMatrix.Realisation.rootPairingBase_cartanMatrix_eq`).

Each finite Cartan matrix has a realisation. If $A$ is invertible over $R$, then `Matrix.IsFiniteCartan.toRealisation` takes $M = N = R^n$, the standard basis vectors as roots and as coroots, and the pairing $\langle x, y \rangle = x \cdot (A y)$.

**Definition (`Matrix.IsFiniteCartan.toRootPairing`).** For a finite Cartan matrix $A$ and a field $k$ of characteristic zero, `Matrix.IsFiniteCartan.toRootPairing k` is the root pairing of the realisation of $A$ on $k^n$.

It is a reduced crystallographic root system, and it is irreducible when $A$ is indecomposable (`Matrix.IsFiniteCartan.isIrreducible_toRootPairing`). Its base has the Cartan matrix $A$ (`Matrix.IsFiniteCartan.rootPairingBase_cartanMatrix_eq`). Together with the Cartan matrix of a base of Volume 29, this shows that the finite Cartan matrices are exactly the Cartan matrices of the bases of finite reduced crystallographic root systems.

#### Common errors

1. `CartanMatrix.A n` is the matrix of type $A_{n-1}$, of size $n$. The matrix of type $A_n$ is `CartanMatrix.A (n + 1)`.
2. The names `CartanMatrix.E₆`, `CartanMatrix.E₇` and `CartanMatrix.E₈` are deprecated. Use `CartanMatrix.E 6`, `CartanMatrix.E 7` and `CartanMatrix.E 8`.
3. `CartanMatrix.E n` is defined for each $n$, but it is of finite type only for $n \le 8$. Do not expect a proof of `Matrix.IsFiniteCartan` for `CartanMatrix.E 9`.

### Exercises

1. (A) Prove that `CartanMatrix.G₂` is a generalized Cartan matrix with `Matrix.IsGeneralizedCartan.mk`, and prove each of the three conditions with the decide tactic.
2. (A) Compute the determinant of `CartanMatrix.A 3` and of `CartanMatrix.A n` for small $n$, and guess the formula.
3. (B) Prove that `CartanMatrix.B 2` is symmetrizable with $d = (1, 2)$.
4. (B) Show that `!![2, -1; -1, 2]` is a finite Cartan matrix, with `Matrix.IsFiniteCartan.mk_of_exists_posDef` and $d = (1, 1)$.
5. (B) Show that the generalized Cartan matrix `!![2, -2; -2, 2]` is not of finite type.
6. (C) Prove from `CartanMatrix.E_det` that `CartanMatrix.E 10` is not of finite type.

### Reference

<?reference?>
