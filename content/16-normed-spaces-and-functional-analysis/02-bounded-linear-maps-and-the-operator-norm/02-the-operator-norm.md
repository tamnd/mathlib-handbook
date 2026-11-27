---
title: The operator norm
kind: theory
modules:
  - Mathlib.Analysis.Normed.Operator.Basic
  - Mathlib.Analysis.Normed.Operator.NormedSpace
  - Mathlib.Analysis.Normed.Operator.CompleteCodomain
  - Mathlib.Analysis.Normed.Ring.Units
  - Mathlib.Analysis.Normed.Operator.LinearIsometry
explains:
  E3: [ContinuousLinearMap.le_opNorm, ContinuousLinearMap.opNorm_le_bound, ContinuousLinearMap.opNorm_comp_le, Units.isOpen, LinearIsometry]
  E2: [ContinuousLinearMap.opNorm_nonneg, ContinuousLinearMap.opNorm_zero_iff, ContinuousLinearMap.norm_id_le, ContinuousLinearMap.opNorm_le_of_lipschitzWith, ContinuousLinearMap.toNormedAddCommGroup, ContinuousLinearMap.toNormedRing, SeparatingDual.completeSpace_continuousLinearMap_iff, Units.add, LinearIsometry.norm_map, LinearIsometry.norm_toContinuousLinearMap, LinearIsometryEquiv]
  E1: auto
families: []
requires: [V07, V13, V15, V16.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The operator norm

### Overview

A bounded linear map $T$ has many bounds $C$ with $\|Tx\| \le C\|x\|$. The least of them is the *operator norm* $\|T\|$. With it the space $L(E, F)$ of continuous linear maps is itself a normed space, and this is the main source of new normed spaces in analysis. This section defines the operator norm, proves that it is a norm and that it is submultiplicative, $\|ST\| \le \|S\|\,\|T\|$, and proves that $L(E, F)$ is complete when $F$ is complete. For $E = F$ complete it then proves that the invertible operators form an open set, by the Neumann series. The section ends with the linear isometries and with the dual space $E^* = L(E, \mathbb{K})$, which is the subject of Chapter 5.

### Definitions

**Definition (Operator norm).** Let $T \in L(E, F)$. Its operator norm is
$$\|T\| = \inf\{\, C \ge 0 : \|Tx\| \le C\|x\| \text{ for all } x \in E \,\}.$$

The set is not empty since $T$ is bounded, and it is closed under limits from above, so the infimum is a minimum: $\|Tx\| \le \|T\|\,\|x\|$ for all $x$. When $E \neq 0$ there are the equivalent formulas
$$\|T\| = \sup_{x \neq 0} \frac{\|Tx\|}{\|x\|} = \sup_{\|x\| \le 1} \|Tx\| = \sup_{\|x\| = 1} \|Tx\|,$$
for a real or complex space $E$. The proof of these formulas is Exercise 2. In practice one computes $\|T\|$ in two steps: an upper bound by an inequality valid for all $x$, and a lower bound by a test vector.

::: mathlib
`ContinuousLinearMap.norm_def` · `Mathlib.Analysis.Normed.Operator.Basic`

Mathlib defines the norm as the infimum of the definition, `‖f‖ = sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖}`. The infimum is used because it works over any nontrivially normed field, where a vector of norm exactly $1$ need not exist. The supremum over the unit ball is `ContinuousLinearMap.sSup_unit_ball_eq_norm` in `Mathlib.Analysis.Normed.Operator.NNNorm`, for `RCLike` scalars.

<?decl ContinuousLinearMap.norm_def?>
:::

**Definition (Linear isometry).** A linear map $T : E \to F$ is a *linear isometry* if $\|Tx\| = \|x\|$ for all $x$. A *linear isometric equivalence* is a bijective linear isometry.

A linear isometry is injective, since $Tx = 0$ gives $\|x\| = 0$, and it is continuous with $\|T\| \le 1$, with equality when $E \neq 0$.

::: mathlib
`LinearIsometry` · `Mathlib.Analysis.Normed.Operator.LinearIsometry`

`E →ₗᵢ[𝕜] F` is a structure that extends `E →ₗ[𝕜] F` with the field `norm_map' : ∀ x, ‖toLinearMap x‖ = ‖x‖`. The lemma `LinearIsometry.norm_map` gives `‖f x‖ = ‖x‖`. The equivalences are `E ≃ₗᵢ[𝕜] F`, the structure `LinearIsometryEquiv`. The conversion to a continuous linear map is `f.toContinuousLinearMap`, and its norm is $1$ when `E` is nontrivial (`LinearIsometry.norm_toContinuousLinearMap`).

<?decl LinearIsometry?>
:::

**Definition (Dual space).** The *dual space* of a normed space $E$ over $\mathbb{K}$ is $E^* = L(E, \mathbb{K})$, the continuous linear functionals with the operator norm $\|f\| = \sup_{\|x\| \le 1} |f(x)|$.

::: mathlib
`StrongDual` · `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic`

`StrongDual 𝕜 E` is an abbreviation for `E →L[𝕜] 𝕜`. It has the normed structure of `E →L[𝕜] 𝕜` from this section. The index of this edition has no declaration `NormedSpace.Dual`, the name of the dual in earlier editions of Mathlib. The canonical map $E \to E^{**}$ is `NormedSpace.inclusionInDoubleDual` in `Mathlib.Analysis.Normed.Module.DoubleDual`, of norm at most $1$ (Chapter 5).

<?decl StrongDual?>
:::

### Theorems and proofs

**Theorem (Basic bounds).** Let $T \in L(E, F)$.

1. $\|Tx\| \le \|T\|\,\|x\|$ for all $x \in E$.
2. If $C \ge 0$ and $\|Tx\| \le C\|x\|$ for all $x$, then $\|T\| \le C$.

*Proof.* (2) is the definition of the infimum. For (1), let $S$ be the set in the definition and $C_n \in S$ with $C_n \to \|T\|$. For fixed $x$, $\|Tx\| \le C_n\|x\|$ for all $n$, and the limit gives $\|Tx\| \le \|T\|\,\|x\|$. $\square$

::: mathlib
`ContinuousLinearMap.le_opNorm` · `Mathlib.Analysis.Normed.Operator.Basic`

`f.le_opNorm x : ‖f x‖ ≤ ‖f‖ * ‖x‖`, the part (1). The variant `le_opNorm_of_le` gives `‖f x‖ ≤ ‖f‖ * c` from `‖x‖ ≤ c`, and `unit_le_opNorm` gives `‖f x‖ ≤ ‖f‖` from `‖x‖ ≤ 1`.

<?decl ContinuousLinearMap.le_opNorm?>
:::

::: mathlib
`ContinuousLinearMap.opNorm_le_bound` · `Mathlib.Analysis.Normed.Operator.Basic`

`f.opNorm_le_bound hC h : ‖f‖ ≤ C` from `hC : 0 ≤ C` and `h : ∀ x, ‖f x‖ ≤ C * ‖x‖`, the part (2). It is the standard way to bound an operator norm from above. For a Lipschitz map the bound is `opNorm_le_of_lipschitzWith`.

<?decl ContinuousLinearMap.opNorm_le_bound?>
:::

**Theorem (The operator norm is a norm).** On $L(E, F)$ the operator norm satisfies $\|T\| \ge 0$, $\|T\| = 0$ if and only if $T = 0$, $\|cT\| = |c|\,\|T\|$, and $\|S + T\| \le \|S\| + \|T\|$.

*Proof.* Nonnegativity is part of the definition. If $\|T\| = 0$, then $\|Tx\| \le 0$ for all $x$ by the last theorem, so $T = 0$ when $F$ is a normed space. For the triangle inequality, $\|(S + T)x\| \le \|Sx\| + \|Tx\| \le (\|S\| + \|T\|)\|x\|$, and part (2) gives $\|S + T\| \le \|S\| + \|T\|$. In the same way $\|(cT)x\| = |c|\,\|Tx\| \le |c|\,\|T\|\,\|x\|$ gives $\|cT\| \le |c|\,\|T\|$. For $c \neq 0$ apply this to $c^{-1}$ and $cT$ to get the reverse inequality, and for $c = 0$ both sides are $0$. $\square$

::: mathlib
`ContinuousLinearMap.toNormedAddCommGroup` · `Mathlib.Analysis.Normed.Operator.NormedSpace`

The instance that makes `E →SL[σ₁₂] F` a normed additive group when `F` is a normed group. The normed space structure follows, and for `E = F` the instance `ContinuousLinearMap.toNormedRing` makes `E →L[𝕜] E` a normed ring. The fact `‖f‖ = 0 ↔ f = 0` is `opNorm_zero_iff`. When `F` is only seminormed, the operator norm is a seminorm.

<?decl ContinuousLinearMap.toNormedAddCommGroup?>
:::

**Theorem (Submultiplicativity).** Let $T \in L(E, F)$ and $S \in L(F, G)$. Then $\|S \circ T\| \le \|S\|\,\|T\|$. In particular $\|T^n\| \le \|T\|^n$ for $T \in L(E, E)$, and $\|\mathrm{id}_E\| \le 1$.

*Proof.* $\|S(Tx)\| \le \|S\|\,\|Tx\| \le \|S\|\,\|T\|\,\|x\|$, and part (2) of the basic bounds gives the first claim. The second follows by induction on $n$. For the identity, $\|x\| \le 1 \cdot \|x\|$. $\square$

::: mathlib
`ContinuousLinearMap.opNorm_comp_le` · `Mathlib.Analysis.Normed.Operator.Basic`

`‖h.comp f‖ ≤ ‖h‖ * ‖f‖`. It is the field `norm_mul_le` of the normed ring `E →L[𝕜] E`. The norm of the identity is `norm_id_le : ‖id 𝕜 E‖ ≤ 1`, and `norm_id : ‖id 𝕜 E‖ = 1` when `E` has a nonzero vector.

<?decl ContinuousLinearMap.opNorm_comp_le?>
:::

**Theorem (Completeness of the space of operators).** If $F$ is a Banach space, then $L(E, F)$ is a Banach space, for every normed space $E$.

*Proof.* Let $(T_n)$ be a Cauchy sequence in $L(E, F)$. For each $x$, $\|T_nx - T_mx\| \le \|T_n - T_m\|\,\|x\|$, so $(T_nx)$ is a Cauchy sequence in $F$. Since $F$ is complete it has a limit, written $Tx$. The map $T$ is linear: $T_n(ax + by) = aT_nx + bT_ny$, and the limit of both sides gives $T(ax + by) = aTx + bTy$, since the operations of $F$ are continuous.

Let $\varepsilon > 0$ and $N$ with $\|T_n - T_m\| \le \varepsilon$ for $n, m \ge N$. For $x \in E$ and $n, m \ge N$,
$$\|T_nx - T_mx\| \le \varepsilon\|x\|.$$
Let $m \to \infty$. Since the norm is continuous, $\|T_nx - Tx\| \le \varepsilon\|x\|$ for each $n \ge N$ and each $x$. Two facts follow. First, $\|Tx\| \le \|T_Nx\| + \varepsilon\|x\| \le (\|T_N\| + \varepsilon)\|x\|$, so $T$ is bounded and $T \in L(E, F)$. Second, $T_n - T$ is bounded with $\|T_n - T\| \le \varepsilon$ for $n \ge N$, so $T_n \to T$ in the operator norm. $\square$

The proof shows the typical pattern of completeness proofs in function spaces: find a pointwise limit, then turn the uniform Cauchy bound into a uniform bound for the limit. Exercise 8 shows that the converse also holds: if $E \neq 0$ and $L(E, F)$ is complete, then $F$ is complete. In particular the dual $E^*$ is complete for every normed space $E$, complete or not.

::: mathlib
`ContinuousLinearMap.instCompleteSpace` · `Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap`

The instance `CompleteSpace (E →SL[σ] F)` from `CompleteSpace F`. It lives in the general theory of topological vector spaces of Volume 14 and covers every sequential space `E`, so in particular every normed space. In the normed setting, `SeparatingDual.completeSpace_continuousLinearMap_iff` in `Mathlib.Analysis.Normed.Operator.CompleteCodomain` gives the equivalence `CompleteSpace (E →L[𝕜] F) ↔ CompleteSpace F` for nontrivial `E` with enough functionals, which is the content of Exercise 8.

<?decl ContinuousLinearMap.instCompleteSpace?>
:::

**Theorem (Neumann series).** Let $R$ be a complete normed ring, for example $L(E, E)$ with $E$ a Banach space, and let $t \in R$ with $\|t\| < 1$. Then $1 - t$ is invertible, with
$$(1 - t)^{-1} = \sum_{n=0}^{\infty} t^n, \qquad \|(1 - t)^{-1}\| \le \|1\| + \frac{\|t\|}{1 - \|t\|}.$$

*Proof.* Since $\|t^n\| \le \|t\|^n$ and $\sum \|t\|^n$ converges, the series $\sum t^n$ converges absolutely, so it converges in $R$ by the criterion of Chapter 1, Section 3. Let $s$ be its sum and $s_N = \sum_{n=0}^{N} t^n$. Then
$$s_N(1 - t) = (1 - t)s_N = 1 - t^{N+1}.$$
Since $\|t^{N+1}\| \to 0$ and multiplication is continuous, the limit gives $s(1 - t) = (1 - t)s = 1$. For the bound, $\|s\| \le \|1\| + \sum_{n \ge 1}\|t\|^n = \|1\| + \|t\|/(1 - \|t\|)$. $\square$

For $R = L(E, E)$ with $E \neq 0$, $\|1\| = 1$ and the bound reads $\|(1 - t)^{-1}\| \le 1/(1 - \|t\|)$.

**Theorem (The units form an open set).** Let $R$ be a complete normed ring and $x$ an invertible element. If $\|y\| < \|x^{-1}\|^{-1}$, then $x + y$ is invertible. So the set of invertible elements is open in $R$.

*Proof.* Write $x + y = x(1 + x^{-1}y)$. Here $\|x^{-1}y\| \le \|x^{-1}\|\,\|y\| < 1$, so $1 + x^{-1}y = 1 - (-x^{-1}y)$ is invertible by the Neumann series, and $x + y$ is a product of two invertible elements. So the ball of radius $\|x^{-1}\|^{-1}$ around $x$ consists of units. $\square$

::: mathlib
`Units.isOpen` · `Mathlib.Analysis.Normed.Ring.Units`

`IsOpen {x : R | IsUnit x}` in a complete normed ring `R`. The explicit unit is `Units.add x t h` from `h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹`. The Neumann series itself is `Units.oneSub t h` and `geom_series_mul_neg` in `Mathlib.Analysis.SpecificLimits.Normed` (Volume 15). The continuity of the inverse at a unit is `NormedRing.inverse_continuousAt` in the same file.

<?decl Units.isOpen?>
:::

### Examples

**Example (A matrix with the max norm).** Let $A = (a_{ij})$ be an $m \times n$ real matrix, seen as a map $(\mathbb{R}^n, \|\cdot\|_\infty) \to (\mathbb{R}^m, \|\cdot\|_\infty)$. Then
$$\|A\| = \max_i \sum_j |a_{ij}|,$$
the largest row sum. Upper bound: $|(Ax)_i| \le \sum_j |a_{ij}|\,|x_j| \le \big(\sum_j|a_{ij}|\big)\|x\|_\infty$. Lower bound: let $i$ be a row with the largest sum and $x_j = \operatorname{sign}(a_{ij})$. Then $\|x\|_\infty \le 1$ and $(Ax)_i = \sum_j |a_{ij}|$. For $A = \begin{pmatrix} 1 & -2 \\ 3 & 0 \end{pmatrix}$, the row sums are $3$ and $3$, so $\|A\| = 3$. With $\|\cdot\|_1$ on both sides the same method gives the largest column sum, here $\max(4, 2) = 4$.

**Example (A diagonal operator on $\ell^2$).** Let $(\lambda_n)$ be a bounded sequence of scalars and $D(x)_n = \lambda_nx_n$ on $\ell^2$. Then $\|Dx\|_2^2 = \sum|\lambda_n|^2|x_n|^2 \le (\sup|\lambda_n|)^2\|x\|_2^2$, so $\|D\| \le \sup_n|\lambda_n|$. The basis vector $e_k$ gives $\|De_k\|_2 = |\lambda_k|$, so $\|D\| \ge |\lambda_k|$ for each $k$, and $\|D\| = \sup_n |\lambda_n|$. For $\lambda_n = 1 - 1/n$ the norm is $1$, but no unit vector $x$ has $\|Dx\|_2 = 1$: the supremum in the formula for $\|D\|$ need not be attained.

**Example (The shift operators).** On $\ell^2$ the right shift $S(x_1, x_2, \dots) = (0, x_1, x_2, \dots)$ is a linear isometry, so $\|S\| = 1$, and it is not surjective. The left shift $L(x_1, x_2, \dots) = (x_2, x_3, \dots)$ has $\|L\| = 1$, with $LS = \mathrm{id}$ and $SL \neq \mathrm{id}$. So in $L(\ell^2, \ell^2)$ an element can have a left inverse without being invertible, which never happens for matrices. By the theorem on units, the ball of radius $1$ around $\mathrm{id}$ consists of invertible operators, and $S$ is at distance $\|S - \mathrm{id}\| \ge 1$ from $\mathrm{id}$. In fact $\|S - \mathrm{id}\| = 2$ (Exercise 6).

**Example (An integral operator).** Let $k : [0,1]^2 \to \mathbb{R}$ be continuous and $(Kf)(s) = \int_0^1 k(s,t)f(t)\,dt$ on $C[0,1]$ with $\|\cdot\|_\infty$. Then $|(Kf)(s)| \le \big(\int_0^1|k(s,t)|\,dt\big)\|f\|_\infty$, so $\|K\| \le \max_s\int_0^1|k(s,t)|\,dt$, the continuous analogue of the largest row sum. If $\|K\| < 1$, the Neumann series solves the integral equation $f - Kf = g$ for each $g$, with $f = \sum_n K^ng$. For $k(s,t) = st/2$, $\|K\| \le \max_s s/4 = 1/4$, and the solution of $f - Kf = g$ depends continuously on $g$ with $\|f\|_\infty \le \frac43\|g\|_\infty$.

### The library around it

The file `Mathlib.Analysis.Normed.Operator.Basic` has the bounds of this section for semilinear maps between seminormed spaces, and the lemmas `opNorm_add_le`, `opNorm_smul_le`, `opNorm_neg`, `ratio_le_opNorm` and `isLeast_opNorm`. The file `Mathlib.Analysis.Normed.Operator.NormedSpace` has the instances for normed spaces and `LinearMap.bound_of_ball_bound`. The file `Mathlib.Analysis.Normed.Operator.Completeness` has the pointwise limits of a bounded family of operators, `ContinuousLinearMap.ofTendstoOfBoundedRange`, used in Chapter 4 with the uniform boundedness principle. The operator norm of a bilinear map is in `Mathlib.Analysis.Normed.Operator.Bilinear`, and the extension of a bounded operator from a dense subspace with the same norm is `ContinuousLinearMap.extend` with `ContinuousLinearMap.opNorm_extend_le`.

Common errors of a learner:

- Forgetting that the supremum in the formula for $\|T\|$ need not be attained.
- Using `‖id 𝕜 E‖ = 1` for the zero space, where the norm is $0$.
- Expecting $L(E, F)$ to be complete with $E$ complete and $F$ not. It is the completeness of $F$ that matters.

### Exercises

1. (A) Compute the norm of $A = \begin{pmatrix} 2 & 1 \\ 0 & -3 \end{pmatrix}$ as a map of $(\mathbb{R}^2, \|\cdot\|_\infty)$ and of $(\mathbb{R}^2, \|\cdot\|_1)$.
2. (A) Prove the formulas $\|T\| = \sup_{x \neq 0}\|Tx\|/\|x\| = \sup_{\|x\| \le 1}\|Tx\|$ for $E \neq 0$ over $\mathbb{R}$ or $\mathbb{C}$.
3. (A) Show that the evaluation $\delta_t(f) = f(t)$ has norm $1$ on $C[0,1]$, and that the integral $I$ of Section 1 has norm $1$.
4. (B) Let $g \in C[0,1]$. Show that the multiplication operator $M_g$ on $C[0,1]$ has norm $\|g\|_\infty$.
5. (B) Show that $\|T^n\|^{1/n}$ converges to $\inf_n\|T^n\|^{1/n}$, using $\|T^{m+n}\| \le \|T^m\|\,\|T^n\|$. Compute the limit for the Volterra operator $(Vf)(s) = \int_0^s f$ on $C[0,1]$, using $\|V^n\| \le 1/n!$.
6. (B) Show that $\|S - \mathrm{id}\| = 2$ for the right shift $S$ on $\ell^2$. Hint: test with $x = (1, -1, 1, -1, \dots, \pm1, 0, \dots)/\sqrt{N}$.
7. (B) Let $E$ be a Banach space and $T \in L(E, E)$ with $\|T\| < 1$. Show that $\|(1 - T)^{-1} - 1\| \le \|T\|/(1 - \|T\|)$.
8. (C) Let $E \neq 0$ and suppose there is $f \in E^*$ with $f \ne 0$. Show that if $L(E, F)$ is complete, then $F$ is complete. Hint: fix $x_0$ with $f(x_0) = 1$ and send $y$ to the map $x \mapsto f(x)y$.
9. (C) Show that the map $x \mapsto x^{-1}$ on the units of a complete normed ring is continuous, from the identity $a^{-1} - b^{-1} = a^{-1}(b - a)b^{-1}$ and the bound of the Neumann series.

### Notes and history

The norm of an operator and the completeness of the space of operators are in Banach's book of 1932. The series $\sum t^n$ for $(1 - t)^{-1}$ carries the name of Carl Neumann, who used it in potential theory in the nineteenth century. The open set of units and the continuity of the inverse are the start of the spectral theory of Banach algebras. The file `Mathlib.Analysis.Normed.Ring.Units` has the author Heather Macbeth. The files `Mathlib.Analysis.Normed.Operator.Basic` and `Mathlib.Analysis.Normed.Operator.NormedSpace` have the authors Jan-David Salchow, Sébastien Gouëzel and Jean Lo. The file `Mathlib.Analysis.Normed.Operator.CompleteCodomain` has the author Sébastien Gouëzel.

### Reference

<?reference?>
