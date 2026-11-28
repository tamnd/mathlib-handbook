---
title: Exponential, logarithm and quaternions
kind: api
modules:
  - Mathlib.Analysis.Normed.Algebra.Exponential
  - Mathlib.Analysis.Normed.Algebra.Logarithm
  - Mathlib.Analysis.Normed.Algebra.MatrixExponential
  - Mathlib.Analysis.Quaternion
  - Mathlib.Analysis.Normed.Algebra.QuaternionExponential
explains:
  E2: [NormedSpace.exp, NormedSpace.expSeries_radius_eq_top, NormedSpace.exp_add_of_commute, NormedSpace.isUnit_exp, NormedSpace.map_exp, NormedSpace.log, Matrix.exp_diagonal, Matrix.exp_conj, Quaternion.instNormedDivisionRingReal, Quaternion.exp_eq]
  E1: auto
families: []
requires: [V06, V07, V14, V15, V16.C01, V16.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Exponential, logarithm and quaternions

### Overview

In a complete normed algebra over $\mathbb{R}$ or $\mathbb{C}$, the series $\exp(x) = \sum_n x^n / n!$ converges for each $x$, since $\|x^n / n!\| \le \|x\|^n / n!$. This defines the exponential of a matrix, of a bounded operator and of a quaternion. Some rules of the real exponential stay true and some fail. When $x$ and $y$ commute, $\exp(x + y) = \exp(x) \exp(y)$, so $\exp(x)$ is a unit with inverse $\exp(-x)$. For matrices that do not commute the rule fails in general. A continuous algebra homomorphism commutes with the exponential, so the exponential of a diagonal matrix is the diagonal matrix of the exponentials of the entries, and $\exp(U A U^{-1}) = U \exp(A) U^{-1}$.

The logarithm is the series $\log(x) = \sum_{n \ge 1} (-1)^{n+1} (x - 1)^n / n$. Mathlib defines it in the same way as the exponential, and for now has only its algebraic properties. The quaternions $\mathbb{H}$ are a normed division algebra over $\mathbb{R}$ and a real inner product space of dimension $4$. For a quaternion $q$ with real part $a$ and imaginary part $v$, the exponential is $e^a (\cos \|v\| + (\sin \|v\| / \|v\|) v)$, the same formula as for complex numbers.

### The library around it

The definition `NormedSpace.exp` takes a topological ring $\mathbb{A}$ and no field. It is the sum of the series `NormedSpace.expSeries 𝕂 𝔸`, whose $n$-th term is $x^n / n!$, with the field $\mathbb{Q}$ chosen inside. It takes a junk value when the series has no sum, and the value $1$ when $\mathbb{A}$ has no structure of a $\mathbb{Q}$-algebra. So the exponential does not depend on a choice of norm or of a field of scalars, and `NormedSpace.expSeries_eq_expSeries_rat` states that the series is the same for each field. The lemmas `NormedSpace.exp_eq_tsum` and `NormedSpace.exp_eq_tsum_div` give the sum with $(n!)^{-1} \cdot x^n$ and with $x^n / n!$. In Mathlib the name is always written with the namespace, since `Real.exp` and `Complex.exp` are separate functions. Volume 15 compares them, and `NormedSpace.ofReal_exp_ℝ_ℝ` is one of the links.

Over $\mathbb{R}$ or $\mathbb{C}$, `NormedSpace.expSeries_radius_eq_top` states that the series has infinite radius. So in a complete algebra `NormedSpace.expSeries_div_hasSum_exp` states that the series converges to $\exp(x)$ for each $x$, and `NormedSpace.norm_expSeries_div_summable` states that it converges absolutely. For a general field, the forms whose names end in of_mem_ball, such as `NormedSpace.exp_add_of_commute_of_mem_ball`, ask that $x$ is in the ball of convergence. Over the $p$-adic numbers this ball is not the whole field. For example, over $\mathbb{Q}_p$ the series converges only when $\|x\| < p^{-1/(p-1)}$, since the norm of $1 / n!$ grows with $n$. Over $\mathbb{R}$ or $\mathbb{C}$, `NormedSpace.expSeries_radius_pos` is a weaker form of the infinite radius, and it is the hypothesis of the lemmas `NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos` and `NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos`, which also hold over other fields. The theorem `NormedSpace.exp_hasFPowerSeriesOnBall` states that the exponential is the sum of its power series on the whole space, and `NormedSpace.exp_continuous` states that it is continuous. Volume 17 gives the general theory of such series.

The algebraic rules are the following. The lemma `NormedSpace.exp_zero` states $\exp(0) = 1$. The theorem `NormedSpace.exp_add_of_commute` states that $\exp(x + y) = \exp(x) \exp(y)$ when $x y = y x$. Its proof uses the Cauchy product of section 1. In a commutative algebra, `NormedSpace.exp_add` drops the condition, and `NormedSpace.exp_sum` gives the form for a finite sum. The lemma `NormedSpace.isUnit_exp` states that $\exp(x)$ is a unit, and `NormedSpace.invOf_exp` and `Ring.inverse_exp` give its inverse $\exp(-x)$. The lemmas `NormedSpace.exp_nsmul` and `NormedSpace.exp_zsmul` state that $\exp(n x) = \exp(x)^n$. With `Commute.exp`, the exponentials of commuting elements commute.

The exponential commutes with maps and with structure. The lemma `NormedSpace.map_exp` states that $f(\exp(x)) = \exp(f(x))$ for each continuous ring homomorphism $f$ of algebras. The lemmas `NormedSpace.exp_conj` and `NormedSpace.exp_units_conj` give the rule for conjugation by a unit. The lemma `NormedSpace.star_exp` states that $\exp(x)^* = \exp(x^*)$, so `IsSelfAdjoint.exp` states that the exponential of a self adjoint element is self adjoint. The lemma `NormedSpace.exp_mem_unitary_of_mem_skewAdjoint` states that the exponential of a skew adjoint element is unitary. The lemma `NormedSpace.exp_mem` states that a closed subalgebra contains the exponential of each of its elements. For products of algebras, `Prod.fst_exp` and `Pi.exp_def` compute the exponential in each coordinate.

The module `Mathlib.Analysis.Normed.Algebra.MatrixExponential` applies these results to matrices. It does not fix a norm on matrices: the lemmas hold for each matrix algebra over $\mathbb{R}$ or $\mathbb{C}$, and the proofs take a norm inside. The lemma `Matrix.exp_diagonal` states that the exponential of a diagonal matrix is diagonal, and `Matrix.exp_blockDiagonal` is the form with blocks. The lemmas `Matrix.exp_transpose` and `Matrix.exp_conjTranspose` give the transposes. The lemma `Matrix.exp_conj` states that $\exp(U A U^{-1}) = U \exp(A) U^{-1}$ for an invertible $U$. With the spectral theorem of Chapter 7, these lemmas compute the exponential of a Hermitian matrix from its eigenvalues. The lemmas `Matrix.exp_add_of_commute`, `Matrix.exp_neg` and `Matrix.isUnit_exp` are the matrix forms of the general rules, and `Matrix.IsHermitian.exp` states that the exponential of a Hermitian matrix is Hermitian.

The module `Mathlib.Analysis.Normed.Algebra.Logarithm` defines `NormedSpace.log` and the series `NormedSpace.logSeries 𝕂 𝔸`. The lemma `NormedSpace.log_eq_tsum` gives the sum, and `NormedSpace.log_one` states $\log(1) = 0$. The other lemmas are `NormedSpace.star_log`, `NormedSpace.log_mem` and `Commute.log`. Mathlib does not yet prove that $\exp(\log(x)) = x$ for $\|x - 1\| < 1$, so the logarithm is a definition with few theorems.

The module `Mathlib.Analysis.Quaternion` puts the norm on the quaternions `ℍ`, written with the notation `Quaternion.termℍ` for `Quaternion ℝ`. The inner product is $\langle a, b \rangle = \operatorname{Re}(a \bar b)$, by `Quaternion.inner_def`, and `Quaternion.normSq_eq_norm_mul_self` relates the norm to `Quaternion.normSq`. The instance `Quaternion.instNormedDivisionRingReal` makes $\mathbb{H}$ a normed division ring, and `Quaternion.instNormedAlgebraReal` and `Quaternion.instCStarRingReal` add the algebra and the star structure. The map `Quaternion.ofComplex` embeds $\mathbb{C}$ into $\mathbb{H}$, and `Quaternion.linearIsometryEquivTuple` identifies $\mathbb{H}$ with the Euclidean space of dimension $4$. The lemma `Quaternion.norm_star` states that conjugation preserves the norm, and the instance `Quaternion.instCompleteSpaceReal` states that $\mathbb{H}$ is complete, so the exponential series converges in it. The module `Mathlib.Analysis.Normed.Algebra.QuaternionExponential` computes the exponential. The lemma `Quaternion.exp_of_re_eq_zero` gives $\exp(q) = \cos \|q\| + (\sin \|q\| / \|q\|) q$ for an imaginary $q$, `Quaternion.exp_eq` gives the general formula, and `Quaternion.norm_exp` states that $\|\exp(q)\| = \exp(\operatorname{Re} q)$.

#### Common errors

1. Using `NormedSpace.exp_add` for matrices. It needs a commutative algebra. For matrices, use `Matrix.exp_add_of_commute` with a proof that the two matrices commute.
2. Writing `exp A` for a matrix after `open Real`. This gives `Real.exp`, which does not accept a matrix. Write `NormedSpace.exp A`.
3. Expecting a theorem on `NormedSpace.log` that holds for the real logarithm, such as $\log(x y) = \log(x) + \log(y)$. Mathlib does not have it yet, and the series is only meaningful for $\|x - 1\| < 1$.

### Exercises

1. (A) Use `Matrix.exp_diagonal` to compute the exponential of the diagonal matrix with entries $1$ and $2$.
2. (A) Show with `NormedSpace.isUnit_exp` that $\exp(A)$ has nonzero determinant for each complex square matrix $A$.
3. (B) For the nilpotent matrix $N = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$, show that $\exp(t N) = 1 + t N$, from `NormedSpace.exp_eq_tsum`.
4. (B) Find two $2 \times 2$ real matrices $A$ and $B$ with $\exp(A + B) \ne \exp(A) \exp(B)$.
5. (B) Use `Quaternion.exp_of_re_eq_zero` to compute $\exp(\pi i)$ for the quaternion unit $i$, and compare with the formula of Euler for complex numbers.
6. (C) Prove `NormedSpace.exp_mem_unitary_of_mem_skewAdjoint` from `NormedSpace.star_exp` and `NormedSpace.exp_add_of_commute`.

### Reference

<?reference?>
