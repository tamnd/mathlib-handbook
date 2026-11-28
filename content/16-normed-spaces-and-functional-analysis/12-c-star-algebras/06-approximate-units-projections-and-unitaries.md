---
title: Approximate units, projections and the unitary group
kind: api
modules:
  - Mathlib.Analysis.CStarAlgebra.ApproximateUnit
  - Mathlib.Analysis.CStarAlgebra.Extreme
  - Mathlib.Analysis.CStarAlgebra.Projection
  - Mathlib.Analysis.CStarAlgebra.Unitary.Connected
  - Mathlib.Analysis.CStarAlgebra.Unitary.Maps
  - Mathlib.Analysis.CStarAlgebra.Unitary.Span
explains:
  E2: [Filter.IsIncreasingApproximateUnit, CStarAlgebra.approximateUnit, CStarAlgebra.increasingApproximateUnit, isStarProjection_iff_mem_extremePoints_setOfPred_nonneg_inter_unitClosedBall, isStarProjection_iff_spectrum_subset_and_isSelfAdjoint, Unitary.argSelfAdjoint, Unitary.joined, Unitary.mem_pathComponentOne_iff, Unitary.mulLeft, CStarAlgebra.span_unitary]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Approximate units, projections and the unitary group

### Overview

A C*-algebra without a unit still has an approximate unit: a net $(e_\lambda)$ of positive elements of norm at most $1$, increasing in the order of Section 3, with $e_\lambda a \to a$ and $a e_\lambda \to a$ for every $a$. In the compact operators on $\ell^2$, the projections onto the first $n$ coordinates form an approximate unit. In $C_0(\mathbb{R})$, functions that are $1$ on $[-n, n]$ and have norm $1$ form one. The canonical construction takes the set $\Lambda$ of positive elements of norm less than $1$, with its order. This set is directed, a fact that needs a nontrivial argument: the map $x \mapsto x (1 + x)^{-1}$ is an order isomorphism from the positive cone onto $\Lambda$, with inverse $y \mapsto y (1 - y)^{-1}$, and the cone is directed because $x, y \le x + y$.

A projection is a self-adjoint idempotent, $p = p^* = p^2$. By the functional calculus, a normal element is a projection if and only if its spectrum is in $\{0, 1\}$. Projections are also the extreme points of the set of positive elements of norm at most $1$, the positive part of the unit ball. For a function algebra $C(X)$ these are the indicator functions of open and closed sets.

The unitaries $u^* u = u u^* = 1$ form a group $U(A)$, a closed subset of the unit sphere. Each self-adjoint $h$ gives a unitary $e^{i h}$, and the path $t \mapsto e^{i t h}$ joins it to $1$. Conversely, if $\|u - 1\| < 2$, then $-1$ is not in the spectrum of $u$, so the principal argument is continuous on the spectrum, and $h = \arg(u)$ by the functional calculus satisfies $u = e^{i h}$. So the ball of radius $2$ around $1$ is path connected, the group is locally path connected, and the path component of $1$ is the set of finite products of exponentials.

Each element is a combination of four unitaries. A proof: if $a$ is self-adjoint with $\|a\| \le 1$, then $u = a + i \sqrt{1 - a^2}$ is unitary, since $a$ and $\sqrt{1 - a^2}$ commute, and $a = (u + u^*) / 2$. Write a general $x$ as $\|x\|$ times the sum of the real and the imaginary part of $x / \|x\|$, and apply this to each part.

### The library around it

The file `Mathlib.Analysis.CStarAlgebra.ApproximateUnit` uses filters instead of nets. The general predicate `Filter.IsApproximateUnit l`, from topological algebra, says that $m x \to m$ and $x m \to m$ along `l` for every `m`. The predicate `Filter.IsIncreasingApproximateUnit l` adds the fields `Filter.IsIncreasingApproximateUnit.eventually_nonneg` and `Filter.IsIncreasingApproximateUnit.eventually_norm`: the elements are eventually positive and of norm at most $1$. The lemma `Filter.IsIncreasingApproximateUnit.toIsApproximateUnit` forgets the extra fields. The lemma `CStarAlgebra.tendsto_mul_left_iff_tendsto_mul_right` says that for a filter of self-adjoint elements, convergence on one side implies it on the other, since $(x m)^* = m^* x$.

The canonical filter is `CStarAlgebra.approximateUnit A`. Its basis, by `CStarAlgebra.hasBasis_approximateUnit`, is the family of sets $\{x : a \le x, \|x\| \le 1\}$ for positive `a` with $\|a\| < 1$, so it is the filter of the order on $\Lambda$ above. The theorem `CStarAlgebra.increasingApproximateUnit` says that it is an increasing approximate unit, and `CStarAlgebra.instNeBotApproximateUnit` says that it is a proper filter. The directedness is `CStarAlgebra.directedOn_nonneg_ball`, and its proof uses `CFC.monotoneOn_one_sub_one_add_inv`, the operator monotonicity of $x \mapsto 1 - (1 + x)^{-1}$, together with `norm_cfcₙ_one_sub_one_add_inv_lt_one`. The convergence $e_\lambda a \to a$ comes from `CStarAlgebra.norm_sub_mul_self_le`, which bounds $\|z - y z\|$ by $\|z^* (1 - x) z\|^{1/2}$ when $x \le y \le 1$. Section 5 uses this filter in `PositiveContinuousLinearMap.tendsto_nhds_opNorm`.

The file `Mathlib.Analysis.CStarAlgebra.Projection` characterizes projections, with the predicate `IsStarProjection p` for $p = p^* = p^2$. The lemma `isStarProjection_iff_spectrum_subset_and_isSelfAdjoint` gives the spectral form, `isStarProjection_iff_isIdempotentElem_and_isStarNormal` says that a normal idempotent is a projection, and `IsIdempotentElem.isSelfAdjoint_iff_isStarNormal` says that an idempotent is self-adjoint if and only if it is normal. The forms with the quasispectrum, such as `isStarProjection_iff_quasispectrum_subset_and_isSelfAdjoint`, apply to non-unital algebras. The file `Mathlib.Analysis.CStarAlgebra.Extreme` proves `isStarProjection_iff_mem_extremePoints_setOfPred_nonneg_inter_unitClosedBall`: the projections are the extreme points of $\{x : 0 \le x\} \cap \overline{B}(0, 1)$, with `Set.extremePoints` from the theory of extreme points.

The file `Mathlib.Analysis.CStarAlgebra.Unitary.Connected` studies the topology of the group `unitary A`. The definition `Unitary.argSelfAdjoint u` is the self-adjoint element $\arg(u)$, computed with the functional calculus and `Complex.arg`. It returns `0` when the argument is not continuous on the spectrum. The lemma `Unitary.norm_sub_one_lt_two_iff` says that $\|u - 1\| < 2$ if and only if $-1$ is not in the spectrum, and `Unitary.spectrum_subset_slitPlane_iff_norm_lt_two` is the form with `Complex.slitPlane`. Under this condition, `expUnitary_argSelfAdjoint` says that `selfAdjoint.expUnitary` of the argument is `u`, and `argSelfAdjoint_expUnitary` is the converse for self-adjoint elements of norm less than $\pi$. The two maps form `Unitary.openPartialHomeomorph`. The norm of the argument is computed by `Unitary.norm_argSelfAdjoint`, with the bound `Unitary.norm_argSelfAdjoint_le_pi`, and `selfAdjoint.norm_sq_expUnitary_sub_one` gives $\|e^{i h} - 1\|^2 = 2 (1 - \cos \|h\|)$.

The path results are `selfAdjoint.joined_one_expUnitary`, which joins $1$ to $e^{i h}$, and `Unitary.path` and `Unitary.joined`, which join two unitaries with $\|u - v\| < 2$. The proof of the second reduces to the first: `Unitary.norm_sub_eq` says $\|u - v\| = \|u v^* - 1\|$, so $u v^* = e^{i h}$, and the path $t \mapsto e^{i t h} v$ joins $v$ to $u$. Then `Unitary.isPathConnected_ball` says that balls of radius less than $2$ are path connected, and `Unitary.instLocallyPathConnectedSpace` follows. The lemma `Unitary.mem_pathComponentOne_iff` says that `u` is in the path component of `1` if and only if it is a finite product of exponential unitaries.

The file `Mathlib.Analysis.CStarAlgebra.Unitary.Maps` turns unitaries into isometries of `A`. The homomorphism `Unitary.mulLeft R A` sends `u` to left multiplication by `u` as a linear isometric equivalence of `A`, and `Unitary.mulRight R A` does the same on the right. The lemmas `Unitary.toLinearEquiv_mulLeft`, `Unitary.mulLeft_trans_mulLeft` and `Unitary.symm_mulLeft` relate them to the group structure.

The file `Mathlib.Analysis.CStarAlgebra.Unitary.Span` proves the decomposition of the overview. The lemma `IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary` says that $a + i \sqrt{1 - a^2}$ is unitary for a self-adjoint `a` with $\|a\| \le 1$, and `selfAdjoint.unitarySelfAddISMul` bundles it. The theorem `CStarAlgebra.norm_smul_two_inv_smul_add_four_unitary` writes $x$ explicitly with four unitaries, `CStarAlgebra.exists_sum_four_unitary` states the existence with coefficients of norm at most $\|x\| / 2$, and `CStarAlgebra.span_unitary` says that the unitaries span `A`.

#### Common errors

1. `CStarAlgebra.approximateUnit A` is a filter, not a sequence. A statement such as $e_n a \to a$ becomes `Tendsto (fun x ↦ x * a) (CStarAlgebra.approximateUnit A) (𝓝 a)`, and a sequential approximate unit exists for separable algebras but not in general.
2. `Unitary.argSelfAdjoint u` is defined for each unitary, but it is meaningful only when $\|u - 1\| < 2$. Lemmas such as `expUnitary_argSelfAdjoint` carry this condition, and without it the value is `0`.
3. `IsStarProjection p` needs both $p^* = p$ and $p^2 = p$. An idempotent need not be self-adjoint: the matrix with rows $(1, 1)$ and $(0, 0)$ is idempotent and not a projection.

### Exercises

1. (A) Prove that a projection in a nontrivial C*-algebra has norm $0$ or $1$, with `isStarProjection_iff_spectrum_subset_and_isSelfAdjoint`.
2. (A) Show that left multiplication by a unitary preserves the norm, with `Unitary.mulLeft`.
3. (B) Prove that the unitaries $u$ and $-u$ have distance $2$, and that $\|u - 1\| < 2$ fails for $u = -1$ in a nontrivial algebra.
4. (B) In $C([0, 1])$, prove that the only projections are $0$ and $1$, with `isStarProjection_iff_spectrum_subset_and_isSelfAdjoint` and the connectedness of $[0, 1]$.
5. (B) Show that the unitary group of a commutative unital C*-algebra is path connected if each unitary is of the form $e^{i h}$, with `selfAdjoint.joined_one_expUnitary`.
6. (C) Prove that a linear functional on a C*-algebra that vanishes on all unitaries is $0$, with `CStarAlgebra.span_unitary`.

### Reference

<?reference?>
