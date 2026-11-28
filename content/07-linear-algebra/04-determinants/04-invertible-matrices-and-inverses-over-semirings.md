---
title: Invertible matrices, integer powers and inverses over semirings
kind: api
modules:
  - Mathlib.LinearAlgebra.Matrix.Invertible
  - Mathlib.LinearAlgebra.Matrix.Nonsingular
  - Mathlib.LinearAlgebra.Matrix.SemiringInverse
  - Mathlib.LinearAlgebra.Matrix.ZPow
explains:
  E2: [Matrix.invOf_add_mul_mul, Matrix.invertibleTranspose, Matrix.detp, Matrix.adjp, Matrix.Nonsingular, Matrix.instIsStablyFiniteRingOfCommSemiring, Matrix.nonsingular_iff_det_mem_nonZeroDivisors, Matrix.linearIndependent_col_iff, Matrix.zpow_add, Matrix.zpow_neg]
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

## Invertible matrices, integer powers and inverses over semirings

### Overview

Section 2 proves that a square matrix over a commutative ring is invertible if and only if its determinant is a unit, and it defines the inverse $A^{-1}$ with the adjugate. This section collects four further topics about inverses. The first is the form of inverses with the class `Invertible` of Volume 3, with the Woodbury identity for the inverse of a perturbed matrix. The second is the integer powers $A^k$ for $k \in \mathbb{Z}$. The third and fourth work over a commutative semiring, such as $\mathbb{N}$, where the determinant has no meaning because there is no subtraction: Mathlib splits the determinant into its positive and negative parts, proves that a one-sided inverse is a two-sided inverse, and characterizes the matrices with linearly independent columns.

### The library around it

#### Inverses with the class Invertible

An instance `Invertible A` holds a chosen inverse `⅟A` with the two equations $A \cdot ⅟A = 1$ and $⅟A \cdot A = 1$. The rewriting lemmas `Matrix.invOf_mul_cancel_left`, `Matrix.mul_invOf_cancel_right` and `Matrix.mul_left_eq_iff_eq_invOf_mul` use the inverse to solve linear equations in matrices.

The transpose and the conjugate transpose of an invertible matrix are invertible.

**Definition (`Matrix.invertibleTranspose`).** For an invertible square matrix $A$ over a commutative semiring, `Matrix.invertibleTranspose A` is the instance `Invertible A.transpose` with the inverse $(⅟A)^T$.

*Proof of the equations.* $A^T (⅟A)^T = (⅟A \cdot A)^T = 1^T = 1$, and the other order is the same. $\square$

The converse is `Matrix.invertibleOfInvertibleTranspose`, and the equivalence of the two classes is `Matrix.transposeInvertibleEquivInvertible`. The version for the conjugate transpose is `Matrix.invertibleConjTranspose`. The statements for units are `Matrix.isUnit_transpose` and `Matrix.isUnit_conjTranspose`, and the formulas for the inverse are `Matrix.transpose_invOf` and `Matrix.conjTranspose_invOf`.

A change of low rank of an invertible matrix has an inverse given by a formula.

**Theorem (`Matrix.invOf_add_mul_mul`).** Let $A$ be an invertible $n \times n$ matrix and $C$ an invertible $m \times m$ matrix over a ring, with $U$ of size $n \times m$ and $V$ of size $m \times n$. If $C^{-1} + V A^{-1} U$ and $A + U C V$ are invertible, then
$$(A + U C V)^{-1} = A^{-1} - A^{-1} U (C^{-1} + V A^{-1} U)^{-1} V A^{-1}.$$

*Proof sketch.* Multiply $A + U C V$ by the right side and expand. The terms with $U$ combine to $U C (C^{-1} + V A^{-1} U)(C^{-1} + V A^{-1} U)^{-1} V A^{-1} = U C V A^{-1}$, which cancels the term $U C V A^{-1}$ of the first product. What remains is $A A^{-1} = 1$. This is `Matrix.add_mul_mul_invOf_mul_eq_one`. $\square$

This is the Woodbury identity. When $m$ is small, it computes the inverse of $A + U C V$ from the inverse of $A$ with the inversion of an $m \times m$ matrix only. The instance `Matrix.invertibleAddMulMul` gives the inverse from the inverses of $A$, $C$ and $C^{-1} + V A^{-1} U$. The variant `Matrix.invOf_add_mul_mul'` is the binomial inverse theorem, which does not need $C$ to be invertible. The case $m = 1$ is the formula of Sherman and Morrison.

#### Integer powers

The inverse $A^{-1}$ of Section 2 is defined for each square matrix over a commutative ring, with the value $0$ when $\det A$ is not a unit. With it, the instance `Matrix.instDivInvMonoid` defines $A^k$ for $k \in \mathbb{Z}$, with $A^{-k} = (A^k)^{-1}$ for $k \in \mathbb{N}$ (`Matrix.zpow_neg_natCast`). The usual laws need the hypothesis that the determinant is a unit.

**Theorem (`Matrix.zpow_add`).** If $\det A$ is a unit, then $A^{m + n} = A^m A^n$ for all integers $m$ and $n$.

*Proof sketch.* For $m, n \ge 0$ this is the law of the powers of a monoid. The unit $A$ of the matrix ring gives a group element $u$ with $u^k = A^k$ for each integer $k$ (`Matrix.coe_units_zpow`), and in a group the law holds for all integers. $\square$

**Theorem (`Matrix.zpow_neg`).** If $\det A$ is a unit, then $A^{-n} = (A^n)^{-1}$ for each integer $n$.

Without the hypothesis these laws can fail: for a singular $A$, $A^{-1} = 0$ and $A^{1 + (-1)} = 1 \ne A \cdot 0$. The laws that hold for all matrices are `Matrix.zpow_add_of_nonneg`, `Matrix.zpow_add_of_nonpos`, `Matrix.inv_zpow` and `Matrix.zpow_neg_one`. The other laws are `Matrix.zpow_mul`, `Matrix.zpow_sub`, `Matrix.inv_zpow'` and the rules for commuting matrices, such as `Matrix.Commute.mul_zpow`. The determinant of a power is a unit exactly when the determinant of $A$ is a unit or the exponent is $0$ (`Matrix.isUnit_det_zpow_iff`). Integer powers commute with the transpose (`Matrix.transpose_zpow`), and a symmetric matrix has symmetric powers (`Matrix.IsSymm.zpow`).

#### Determinants over a semiring

Over a commutative semiring the formula of Leibniz has the signs $\pm 1$, which are not available. Mathlib keeps the two halves of the sum apart.

**Definition (`Matrix.detp`).** For a unit $s = \pm 1$ of $\mathbb{Z}$, `Matrix.detp s A` is the sum $\sum_{\sigma} \prod_k A_{k, \sigma(k)}$ over the permutations $\sigma$ of sign $s$.

Over a ring, $\det A$ is `Matrix.detp 1 A - Matrix.detp (-1) A`. The lemmas `Matrix.detp_transpose`, `Matrix.detp_smul`, `Matrix.detp_one_diagonal` and `Matrix.detp_neg_one_diagonal` are the analogues of the rules of Section 1. If two rows are equal, the two halves are equal (`Matrix.detp_eq_of_row_eq`).

**Definition (`Matrix.adjp`).** For $s = \pm 1$, `Matrix.adjp s A` is the half of the adjugate matrix with the terms of sign $s$.

The adjugate identity $A \operatorname{adj} A = \det A \cdot 1$ of Section 2 becomes an identity without subtraction, `Matrix.mul_adjp_add_detp`: $A \operatorname{adjp}_1 A + \operatorname{detp}_{-1} A \cdot 1 = A \operatorname{adjp}_{-1} A + \operatorname{detp}_1 A \cdot 1$. The proof of the main theorem uses it.

**Theorem (`Matrix.instIsStablyFiniteRingOfCommSemiring`).** Over a commutative semiring, $A B = 1$ implies $B A = 1$ for square matrices.

*Proof sketch.* Apply the identity `Matrix.detp_smul_add_adjp` to $A B = 1$ and multiply it by $B$ on the left. The two halves are multiplicative up to mixed terms, and `Matrix.isAddUnit_detp_mul_detp` says that these mixed terms have an additive inverse, so they can be cancelled. The equation that remains is $B A = 1$. $\square$

In the language of the library, each commutative semiring is a stably finite ring. Over a commutative ring the theorem follows from determinants, but the proof over a semiring needs the split determinant.

#### Nonsingular matrices over semirings

Over a ring, the determinant $d$ of $A$ is not a zero divisor when $(a - b) d = 0$ implies $a = b$. Over a semiring the same condition is written with the two halves.

**Definition (`Matrix.Nonsingular`).** A square matrix $A$ over a commutative semiring is nonsingular when $a \operatorname{detp}_1 A + b \operatorname{detp}_{-1} A = b \operatorname{detp}_1 A + a \operatorname{detp}_{-1} A$ implies $a = b$.

The condition on $a$ and $b$ is `Matrix.IsDetpBalanced`. Over a commutative ring the definition becomes the expected one.

**Theorem (`Matrix.nonsingular_iff_det_mem_nonZeroDivisors`).** Over a commutative ring, $A$ is nonsingular if and only if $\det A$ is not a zero divisor.

Over a domain this means $\det A \ne 0$ (`Matrix.nonsingular_iff_det_ne_zero`). The module `Mathlib.LinearAlgebra.Matrix.Nonsingular` proves the results of Tan on free sets in semimodules.

**Theorem (`Matrix.linearIndependent_col_iff`).** Over a commutative semiring with cancellative addition, the columns of a square matrix $A$ are linearly independent if and only if $A$ is nonsingular.

The direction from independence to nonsingularity, `Matrix.Nonsingular.of_linearIndependent_col`, holds without the cancellation. The same is true for rows (`Matrix.linearIndependent_row_iff`), so `Matrix.linearIndependent_col_iff_row` says that the columns are independent if and only if the rows are. The matrix is nonsingular if and only if multiplication by it on the left is injective (`Matrix.isLeftRegular_iff_nonsingular`), and products of nonsingular matrices are nonsingular (`Matrix.nonsingular_mul_iff`). A consequence is `CommSemiring.strongRankCondition_of_nontrivial`: each nontrivial commutative semiring has the strong rank condition of Chapter 2 Section 5.

#### Common errors

1. `A⁻¹` is defined for all square matrices, with the value $0$ for a singular matrix. Lemmas such as `Matrix.zpow_add` need the hypothesis `IsUnit A.det`; check it before the rewrite.
2. `⅟A` needs an instance `Invertible A`, and `A⁻¹` does not. To change between them, use `Matrix.invOf_eq_nonsing_inv` of Section 2.
3. `Matrix.det` needs a commutative ring, so it is not available for matrices over $\mathbb{N}$. Use `Matrix.detp` for the two halves of the determinant.

### Exercises

1. (A) Compute `Matrix.detp 1 A` and `Matrix.detp (-1) A` for $A$ = `!![a, b; c, d]`.
2. (A) Show that $A^{-2} = (A^{-1})^2$ for each square matrix over a commutative ring.
3. (B) Prove the formula of Sherman and Morrison: for an invertible $A$ and vectors $u$, $v$ with $1 + v^T A^{-1} u$ a unit, $(A + u v^T)^{-1} = A^{-1} - \frac{A^{-1} u v^T A^{-1}}{1 + v^T A^{-1} u}$.
4. (B) Find a singular $2 \times 2$ real matrix $A$ with $A^{1 + (-1)} \ne A \cdot A^{-1}$.
5. (B) Show that a square matrix over $\mathbb{N}$ with a right inverse over $\mathbb{N}$ is a permutation matrix.
6. (C) Prove that the matrix `!![2, 1; 1, 1]` over $\mathbb{N}$ is nonsingular and has no inverse over $\mathbb{N}$.

### Reference

<?reference?>
