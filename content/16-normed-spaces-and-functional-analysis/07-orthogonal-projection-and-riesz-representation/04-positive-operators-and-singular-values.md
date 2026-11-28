---
title: Positive operators and singular values
kind: api
modules:
  - Mathlib.Analysis.InnerProductSpace.Positive
  - Mathlib.Analysis.InnerProductSpace.SingularValues
  - Mathlib.Analysis.InnerProductSpace.Trace
  - Mathlib.Analysis.InnerProductSpace.JointEigenspace
  - Mathlib.Analysis.InnerProductSpace.Semisimple
  - Mathlib.Analysis.InnerProductSpace.MeanErgodic
  - Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
explains:
  E2: [LinearMap.IsPositive, ContinuousLinearMap.IsPositive, ContinuousLinearMap.isPositive_iff', ContinuousLinearMap.IsPositive.adjoint_conj, ContinuousLinearMap.le_def, LinearMap.singularValues, LinearMap.trace_eq_sum_inner, LinearMap.IsSymmetric.directSum_isInternal_of_commute, ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection, ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C03, V16.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Positive operators and singular values

### Overview

Section 3 defines the adjoint and the symmetric operators, and proves the spectral theorem in finite dimension. This section continues with the operators $T$ for which $\langle T x, x \rangle \ge 0$ for all $x$. These positive operators give an order on operators, the Loewner order, and they are the operators of the form $S^* S$. In finite dimension, the eigenvalues of $T^* T$ are the squares of the singular values of $T$, and the trace of $T$ is $\sum_i \langle b_i, T b_i \rangle$ for every orthonormal basis.

The section also collects four small modules on symmetric and bounded operators. A family of commuting symmetric operators has a common orthogonal decomposition into eigenspaces. A symmetric operator is semisimple. The averages $\frac{1}{n} \sum_{k < n} f^k x$ of a contraction converge to the projection of $x$ on the fixed vectors. The weak operator topology on bounded operators is the topology of convergence of all $\langle y, T x \rangle$.

### The library around it

#### Positive operators

Let $E$ be an inner product space over $\mathbb{K}$. The module `Mathlib.Analysis.InnerProductSpace.Positive` defines two predicates with the same content. `LinearMap.IsPositive T` is for a linear map $T : E \to E$, and `ContinuousLinearMap.IsPositive T` is for a bounded one. Each says that $T$ is symmetric and that $\mathrm{Re} \langle T x, x \rangle \ge 0$ for all $x$. The lemma `ContinuousLinearMap.isPositive_iff` gives the useful form: $T$ is symmetric and $0 \le \langle T x, x \rangle$ in $\mathbb{K}$ with its order. In a Hilbert space, symmetric is the same as self adjoint, so `ContinuousLinearMap.isPositive_iff'` reads
$$T \ge 0 \iff T = T^* \text{ and } \langle T x, x \rangle \ge 0 \text{ for all } x.$$
Over $\mathbb{C}$, the condition of symmetry is automatic: `ContinuousLinearMap.isPositive_iff_complex` says that $T$ is positive when each $\langle T x, x \rangle$ is real and nonnegative. The reason is polarization: the values $\langle T x, x \rangle$ determine $\langle T x, y \rangle$ for all $x, y$, so if they are real, then $\langle T x, y \rangle = \overline{\langle T y, x \rangle}$. The lemmas `ContinuousLinearMap.isPositive_toLinearMap_iff` and `LinearMap.isPositive_toContinuousLinearMap_iff` move between the two predicates.

The positive operators form a convex cone that contains the identity and all products $S^* S$.

| Lean name | Statement |
|---|---|
| `ContinuousLinearMap.isPositive_id` | the identity is positive |
| `ContinuousLinearMap.IsPositive.add` | a sum of positive operators is positive |
| `ContinuousLinearMap.IsPositive.smul_of_nonneg` | $c T \ge 0$ for $T \ge 0$ and $c \ge 0$ |
| `ContinuousLinearMap.IsPositive.adjoint_conj` | $S^* T S \ge 0$ for $T \ge 0$ |
| `ContinuousLinearMap.IsPositive.conj_adjoint` | $S T S^* \ge 0$ for $T \ge 0$ |
| `ContinuousLinearMap.isPositive_self_comp_adjoint` | $S S^* \ge 0$ |
| `LinearMap.isPositive_adjoint_comp_self` | $S^* S \ge 0$ in finite dimension |
| `InnerProductSpace.isPositive_rankOne_self` | the rank one operator $y \mapsto \langle x, y \rangle x$ is positive |
| `ContinuousLinearMap.IsPositive.of_isStarProjection` | an orthogonal projection is positive |
| `ContinuousLinearMap.IsPositive.orthogonalProjectionOnto_comp` | $P_U T \iota_U \ge 0$ on $U$ for $T \ge 0$ |

The proof of `ContinuousLinearMap.IsPositive.adjoint_conj` is one line: $\langle S^* T S x, x \rangle = \langle T (S x), S x \rangle \ge 0$, and $(S^* T S)^* = S^* T^* S = S^* T S$. With $T = 1$ it gives $S^* S \ge 0$.

The Loewner order is $S \le T$ when $T - S$ is positive. The instances `ContinuousLinearMap.instLoewnerPartialOrder` and `LinearMap.instLoewnerPartialOrder` install it, and `ContinuousLinearMap.le_def` and `ContinuousLinearMap.nonneg_iff_isPositive` unfold it. It is a partial order: antisymmetry holds because a symmetric operator with $\langle T x, x \rangle = 0$ for all $x$ is $0$. The order is compatible with addition and with scalars $c \ge 0$, by the instances `ContinuousLinearMap.instIsOrderedAddMonoidId` and `ContinuousLinearMap.instIsOrderedModule`. It is not a total order: on $\mathbb{R}^2$, the diagonal operators with entries $(1, 0)$ and $(0, 1)$ are not comparable. The lemma `ContinuousLinearMap.norm_map_le_norm_iff_le` says that $\lVert p x \rVert \le \lVert x \rVert$ for all $x$ if and only if $p^* p \le 1$.

In finite dimension, the module connects positivity with eigenvalues and matrices. A positive operator has nonnegative eigenvalues (`LinearMap.IsPositive.nonneg_eigenvalues`) and a nonnegative trace (`LinearMap.IsPositive.trace_nonneg`). `ContinuousLinearMap.isPositive_iff_eq_sum_rankOne` says that $T \ge 0$ exactly when $T = \sum_i \langle u_i, \cdot \rangle u_i$ for finitely many vectors $u_i$: take the $u_i = \sqrt{\lambda_i} e_i$ for an orthonormal basis of eigenvectors $e_i$. For matrices, `Matrix.isPositive_toEuclideanLin_iff` says that the operator of a matrix $A$ on Euclidean space is positive if and only if $A$ is positive semidefinite. The trace is a positive linear map on operators, `LinearMap.tracePositiveLinearMap`.

For an idempotent $p$ on a Hilbert space, `ContinuousLinearMap.IsIdempotentElem.TFAE` lists four equivalent conditions: $(\mathrm{range}\, p)^\perp = \ker p$, $p$ is normal, $p$ is self adjoint, and $p$ is positive. So for an idempotent, each of these says that $p$ is an orthogonal projection. The lemma `Submodule.starProjection_inj` says that two closed subspaces with the same orthogonal projection are equal.

#### Singular values and the trace

Let $T : E \to F$ be a linear map between finite dimensional inner product spaces. The operator $T^* T$ is positive, so its eigenvalues are real and nonnegative. The module `Mathlib.Analysis.InnerProductSpace.SingularValues` defines `LinearMap.singularValues T : ℕ →₀ ℝ`, the sequence $\sigma_0 \ge \sigma_1 \ge \dots$ of the square roots of these eigenvalues in decreasing order, extended by $0$. The lemma `LinearMap.singularValues_of_lt` says $\sigma_i = \sqrt{\lambda_i}$ for $i < \dim E$, where $\lambda_i$ are the eigenvalues of $T^* T$ in decreasing order, and `LinearMap.singularValues_of_finrank_le` says $\sigma_i = 0$ for $i \ge \dim E$.

| Lean name | Statement |
|---|---|
| `LinearMap.singularValues_nonneg` | $\sigma_i \ge 0$ |
| `LinearMap.singularValues_antitone` | $\sigma_i$ is decreasing in $i$ |
| `LinearMap.support_singularValues` | $\sigma_i \ne 0$ exactly for $i < \operatorname{rank} T$ |
| `LinearMap.card_support_singularValues` | the number of nonzero singular values is the rank of $T$ |
| `LinearMap.singularValues_eq_zero_iff` | all singular values are $0$ only for $T = 0$ |
| `LinearMap.injective_iff_forall_lt_finrank_singularValues_pos` | $T$ is injective if and only if $\sigma_i > 0$ for $i < \dim E$ |
| `LinearMap.hasEigenvalue_adjoint_comp_self_sq_singularValues` | $\sigma_i^2$ is an eigenvalue of $T^* T$ for $i < \dim E$ |

The rank statement holds because $\ker(T^* T) = \ker T$: if $T^* T x = 0$, then $\lVert T x \rVert^2 = \langle T^* T x, x \rangle = 0$. So the number of nonzero eigenvalues of $T^* T$, counted with multiplicity, is $\dim E - \dim \ker T = \operatorname{rank} T$. Section 6 of Chapter 6 uses singular values for the norm determinant.

The module `Mathlib.Analysis.InnerProductSpace.Trace` gives the trace in an orthonormal basis. The theorem `LinearMap.trace_eq_sum_inner` says
$$\operatorname{tr} T = \sum_i \langle b_i, T b_i \rangle$$
for every orthonormal basis $(b_i)$. The proof: the diagonal entry $(i, i)$ of the matrix of $T$ in the basis $b$ is the coefficient of $b_i$ in $T b_i$, and this coefficient is $\langle b_i, T b_i \rangle$ because $b$ is orthonormal. The other results are `InnerProductSpace.trace_rankOne`, the trace of the rank one operator $\langle y, \cdot \rangle x$ is $\langle y, x \rangle$, and `LinearMap.IsSymmetric.trace_eq_sum_eigenvalues`, the trace of a symmetric operator is the sum of its eigenvalues.

#### Commuting symmetric operators and semisimplicity

The module `Mathlib.Analysis.InnerProductSpace.JointEigenspace` proves the spectral theorem for commuting families. Let $A$ and $B$ be symmetric operators on a finite dimensional space with $A B = B A$. Then `LinearMap.IsSymmetric.directSum_isInternal_of_commute` says that $E$ is the internal direct sum of the joint eigenspaces $E_\alpha(A) \cap E_\gamma(B)$, and `LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace` says that these spaces are orthogonal. The proof: $B$ commutes with $A$, so $B$ maps each eigenspace $E_\alpha(A)$ into itself. The restriction of $B$ to $E_\alpha(A)$ is symmetric, so the spectral theorem of Section 3 splits $E_\alpha(A)$ into eigenspaces of $B$. The forms `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute` and `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute` do the same for a family $(T_i)$ of pairwise commuting symmetric operators, with the joint eigenspaces $\bigcap_i E_{\chi(i)}(T_i)$.

The module `Mathlib.Analysis.InnerProductSpace.Semisimple` has two lemmas. `LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule` says that for a symmetric $T$, the orthogonal complement of an invariant subspace is invariant: if $T p \subseteq p$ and $y \perp p$, then $\langle T y, x \rangle = \langle y, T x \rangle = 0$ for $x \in p$. So each invariant subspace has an invariant complement, and `LinearMap.IsSymmetric.isFinitelySemisimple` concludes that $T$ is semisimple in the sense of Volume 7.

#### The mean ergodic theorem

The module `Mathlib.Analysis.InnerProductSpace.MeanErgodic` proves the mean ergodic theorem of von Neumann. Let $f$ be a bounded operator on a Hilbert space with $\lVert f \rVert \le 1$. Then `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` says that for every $x$,
$$\frac{1}{n} \sum_{k=0}^{n-1} f^k x \to P x,$$
where $P$ is the orthogonal projection onto the fixed space $\{x : f x = x\}$. The averages are `birkhoffAverage` of Volume 21. Here is a sketch. For $x = y - f y$, the sum telescopes, and the average is $\frac{1}{n}(y - f^n y)$, which tends to $0$. For a fixed $x$, the average is $x$. The closure of the range of $1 - f$ is the orthogonal complement of the fixed space, because for a contraction $f x = x$ if and only if $f^* x = x$. A limit argument with the bound $\lVert f^k \rVert \le 1$ ends the proof. The general form `LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure` states the same argument in a normed space.

#### The weak operator topology

The type `E →WOT[𝕜] F`, named `ContinuousLinearMapWOT`, is a copy of the space of bounded operators with the weak operator topology. Chapter 8 defines it for topological vector spaces with the topology of the functionals $T \mapsto \ell(T x)$. The module `Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology` specializes it to a Hilbert space $F$: by the theorem of Riesz of Section 2, each functional on $F$ is $\langle y, \cdot \rangle$, so the topology is the topology of the numbers $\langle y, T x \rangle$. The lemma `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto` says
$$T_\alpha \to T \text{ in the weak operator topology} \iff \langle y, T_\alpha x \rangle \to \langle y, T x \rangle \text{ for all } x, y.$$
The lemmas `ContinuousLinearMapWOT.continuous_iff`, `ContinuousLinearMapWOT.continuousAt_iff` and `ContinuousLinearMapWOT.continuousOn_iff` give the same test for continuity, and `ContinuousLinearMapWOT.ext_inner` says that the numbers $\langle y, T x \rangle$ determine $T$. On $F \to F$, the instances `ContinuousLinearMapWOT.instStarRingId` and `ContinuousLinearMapWOT.instContinuousStarId` say that the adjoint is continuous in this topology, because $\langle y, T^* x \rangle = \overline{\langle x, T y \rangle}$. The adjoint is not continuous for the strong operator topology, so this is a property of the weak topology only.

#### Common errors

1. `LinearMap.IsPositive` and `ContinuousLinearMap.IsPositive` are two predicates. A lemma for one does not apply to the other without `ContinuousLinearMap.isPositive_toLinearMap_iff`.
2. The relation `S ≤ T` on operators is the Loewner order, not a comparison of norms. `0 ≤ T` means that $T$ is positive, and `ContinuousLinearMap.nonneg_iff_isPositive` converts it.
3. `LinearMap.singularValues T` is a function on all of `ℕ` with finite support. It is $0$ from the rank of $T$ on, and the index starts at $0$ for the largest singular value.

### Exercises

1. (A) Prove that $T^* T \le \lVert T \rVert^2 \cdot 1$ in the Loewner order.
2. (A) Use `LinearMap.trace_eq_sum_inner` to prove that $\operatorname{tr}(T^* T) = \sum_i \lVert T b_i \rVert^2$ for an orthonormal basis $(b_i)$.
3. (B) Compute the singular values of the operator of the matrix $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ on $\mathbb{R}^2$.
4. (B) Prove that $0 \le S \le T$ implies $\lVert S \rVert \le \lVert T \rVert$ for bounded operators on a Hilbert space.
5. (B) Let $f$ be a unitary operator on a Hilbert space. Prove that the fixed space of $f$ and the closure of the range of $1 - f$ are orthogonal complements.
6. (C) Prove that the unit ball of bounded operators on a Hilbert space is compact in the weak operator topology.

### Reference

<?reference?>
