---
title: Best approximation and orthogonal projection
kind: theory
modules:
  - Mathlib.Analysis.InnerProductSpace.Projection.Minimal
  - Mathlib.Analysis.InnerProductSpace.Projection.Basic
  - Mathlib.Analysis.InnerProductSpace.Projection.Submodule
  - Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
  - Mathlib.Analysis.InnerProductSpace.Projection.Reflection
explains:
  E3: [exists_norm_eq_iInf_of_complete_convex, norm_eq_iInf_iff_real_inner_le_zero, Submodule.HasOrthogonalProjection, Submodule.orthogonalProjectionOnto]
  E2: [Submodule.exists_norm_eq_iInf_of_complete_subspace, Submodule.norm_eq_iInf_iff_inner_eq_zero, Submodule.HasOrthogonalProjection.ofCompleteSpace, Submodule.instHasOrthogonalProjectionOfCompleteSpace, Submodule.starProjection, Submodule.starProjection_apply, Submodule.sub_starProjection_mem_orthogonal, Submodule.starProjection_minimal, Submodule.orthogonalProjectionOnto_norm_le, Submodule.starProjection_norm_le, Submodule.norm_sq_eq_add_norm_sq_starProjection, Submodule.isCompl_orthogonal, Submodule.exists_add_mem_mem_orthogonal, Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal_eq_closure, Submodule.orthogonal_eq_bot_iff]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Best approximation and orthogonal projection

### Overview

In a Hilbert space each nonempty closed convex set has exactly one point nearest to a given vector. The proof uses the parallelogram law to show that a minimizing sequence is Cauchy, and completeness gives the limit. For a closed subspace $K$ the nearest point $Pv$ is characterized by $v - Pv \perp K$. The map $P$ is the orthogonal projection: a linear operator of norm at most $1$, with $E = K \oplus K^\perp$. In a Banach space the nearest point can fail to exist, and this is the first place where the geometry of a Hilbert space has no analogue for Banach spaces.

### Definitions

**Definition (nearest point).** Let $C$ be a subset of a normed space $E$ and $u \in E$. A *nearest point* of $C$ to $u$ is $v \in C$ with $\|u - v\| = d(u, C) = \inf_{w \in C}\|u - w\|$.

**Definition (orthogonal projection).** Let $K$ be a subspace of an inner product space $E$. A map $P : E \to K$ is the *orthogonal projection* onto $K$ if $v - Pv \in K^\perp$ for each $v \in E$.

::: mathlib
`Submodule.HasOrthogonalProjection` · `Mathlib.Analysis.InnerProductSpace.Projection.Basic`

`K.HasOrthogonalProjection` is a class in `Prop` with one field, `exists_orthogonal : ∀ v, ∃ w ∈ K, v - w ∈ K.orthogonal`. It is the hypothesis under which the projection exists. The instance `HasOrthogonalProjection.ofCompleteSpace` gives it when `K` is complete, and `instHasOrthogonalProjectionOfCompleteSpace` gives it for a `ClosedSubmodule` of a complete space. With the class, Mathlib states the projection for complete subspaces of an incomplete space, such as finite dimensional subspaces.

<?decl Submodule.HasOrthogonalProjection?>
:::

### Theorems and proofs

**Theorem (nearest point).** Let $C$ be a nonempty complete convex subset of an inner product space $E$ and $u \in E$. There is a unique nearest point of $C$ to $u$.

*Proof.* Let $\delta = d(u, C)$ and pick $w_n \in C$ with $\|u - w_n\|^2 < \delta^2 + 1/n$. The parallelogram law for $u - w_n$ and $u - w_m$ gives
$$\|w_n - w_m\|^2 = 2\|u - w_n\|^2 + 2\|u - w_m\|^2 - 4\Big\|u - \frac{w_n + w_m}{2}\Big\|^2.$$
The midpoint is in $C$ by convexity, so the last norm is at least $\delta$. Hence $\|w_n - w_m\|^2 \le 2/n + 2/m$, and $(w_n)$ is Cauchy. Since $C$ is complete, $w_n \to v \in C$, and $\|u - v\| = \delta$ by continuity. If $v'$ is a second nearest point, the same identity with $v, v'$ in place of $w_n, w_m$ gives $\|v - v'\|^2 \le 2\delta^2 + 2\delta^2 - 4\delta^2 = 0$. $\square$

::: mathlib
`exists_norm_eq_iInf_of_complete_convex` · `Mathlib.Analysis.InnerProductSpace.Projection.Minimal`

`exists_norm_eq_iInf_of_complete_convex hne hcomp hconv u : ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖` for a real inner product space and `K : Set F` with `K.Nonempty`, `IsComplete K` and `Convex ℝ K`. The proof is the proof of the text with the sequence `δ + 1 / (n + 1)`. The infimum is over the subtype `K`. The version for a subspace over `𝕜` is `Submodule.exists_norm_eq_iInf_of_complete_subspace`.

<?decl exists_norm_eq_iInf_of_complete_convex?>
:::

**Theorem (characterization).** Let $E$ be a real inner product space, $C \subseteq E$ convex, $u \in E$ and $v \in C$. Then $v$ is a nearest point of $C$ to $u$ if and only if $\langle u - v, w - v \rangle \le 0$ for each $w \in C$. If $C = K$ is a subspace over $\mathbb{K}$, the condition is $u - v \in K^\perp$.

*Proof.* For $w \in C$ and $t \in (0, 1]$, the point $v + t(w - v)$ is in $C$, and
$$\|u - v - t(w - v)\|^2 = \|u - v\|^2 - 2t\langle u - v, w - v \rangle + t^2\|w - v\|^2.$$
If $v$ is nearest, the left side is at least $\|u - v\|^2$, so $2\langle u - v, w - v \rangle \le t\|w - v\|^2$, and $t \to 0$ gives the inequality. Conversely, with $t = 1$ the inequality gives $\|u - w\|^2 \ge \|u - v\|^2$. For a subspace, $w - v$ runs over all of $K$, and so does $-(w - v)$, so the inequality for $\pm$ gives $\operatorname{Re}\langle u - v, z \rangle = 0$ for $z \in K$. With $iz$ in place of $z$ in the complex case, $\langle u - v, z \rangle = 0$. $\square$

::: mathlib
`norm_eq_iInf_iff_real_inner_le_zero` · `Mathlib.Analysis.InnerProductSpace.Projection.Minimal`

`norm_eq_iInf_iff_real_inner_le_zero hconv hv : ‖u - v‖ = ⨅ w : K, ‖u - w‖ ↔ ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0`. The form for a subspace is `Submodule.norm_eq_iInf_iff_inner_eq_zero K hv : ‖u - v‖ = ⨅ w : K, ‖u - w‖ ↔ ∀ w ∈ K, ⟪u - v, w⟫_𝕜 = 0`.

<?decl norm_eq_iInf_iff_real_inner_le_zero?>
:::

**Theorem (orthogonal projection).** Let $K$ be a complete subspace of an inner product space $E$. For each $v$ let $Pv$ be the nearest point of $K$ to $v$. Then $P$ is linear, $v - Pv \in K^\perp$, $\|v\|^2 = \|Pv\|^2 + \|v - Pv\|^2$, $\|Pv\| \le \|v\|$, and $Pv = v$ for $v \in K$. Also $E = K \oplus K^\perp$, $K^{\perp\perp} = K$, and $K^\perp = \{0\}$ only if $K = E$.

*Proof.* The characterization gives $v - Pv \in K^\perp$, and $Pv$ is the only $w \in K$ with $v - w \in K^\perp$, since two such $w, w'$ have $w - w' \in K \cap K^\perp = \{0\}$. For linearity, $av + bv' - (aPv + bPv') = a(v - Pv) + b(v' - Pv') \in K^\perp$, so $P(av + bv') = aPv + bPv'$. Pythagoras for $Pv \perp v - Pv$ gives the norm identity and the bound. For $v \in K$, $v$ is its own nearest point. The decomposition $v = Pv + (v - Pv)$ and $K \cap K^\perp = \{0\}$ give $E = K \oplus K^\perp$. If $v \in K^{\perp\perp}$, then $v - Pv \in K^\perp$ and $v - Pv \perp K^\perp$, since $v \in K^{\perp\perp}$ and $Pv \in K \subseteq K^{\perp\perp}$; so $v = Pv \in K$. If $K^\perp = \{0\}$, then $v = Pv \in K$ for each $v$. $\square$

**Corollary.** In a Hilbert space, $K^{\perp\perp} = \overline{K}$ for each subspace $K$, and $K$ is dense if and only if $K^\perp = \{0\}$.

*Proof.* $\overline{K}$ is closed, hence complete, and $K^\perp = \overline{K}^\perp$ by Chapter 6, Section 2. So $K^{\perp\perp} = \overline{K}^{\perp\perp} = \overline{K}$. The second statement is the theorem for $\overline{K}$. $\square$

::: mathlib
`Submodule.orthogonalProjectionOnto` · `Mathlib.Analysis.InnerProductSpace.Projection.Basic`

`K.orthogonalProjectionOnto : E →L[𝕜] K` under `[K.HasOrthogonalProjection]`, with values in the subtype. The same map with values in `E` is `K.starProjection : E →L[𝕜] E`, and `starProjection_apply` relates the two. The old name `Submodule.orthogonalProjection` is deprecated in favour of `orthogonalProjectionOnto`. The facts of the theorem are `sub_starProjection_mem_orthogonal`, `starProjection_minimal`, `norm_sq_eq_add_norm_sq_starProjection`, `orthogonalProjectionOnto_norm_le`, `starProjection_norm_le`, `isCompl_orthogonal`, `exists_add_mem_mem_orthogonal`, `orthogonal_orthogonal` and `orthogonal_eq_bot_iff`. The corollary is `orthogonal_orthogonal_eq_closure`.

<?decl Submodule.orthogonalProjectionOnto?>
:::

### Examples

**Example (projection onto a line).** For a unit vector $e$, the projection onto $\mathbb{K}e$ is $Pv = \langle e, v \rangle e$, since $\langle e, v - \langle e, v \rangle e \rangle = 0$. For a finite orthonormal family $e_1, \dots, e_n$ spanning $K$, $Pv = \sum_k \langle e_k, v \rangle e_k$. In $\mathbb{R}^3$ with $e = (1, 1, 1)/\sqrt3$ and $v = (1, 2, 6)$, $Pv = 3(1, 1, 1)$ and $v - Pv = (-2, -1, 3)$, with sum of coordinates $0$.

**Example (least squares).** Let $A$ be a real $m \times n$ matrix of rank $n$ and $b \in \mathbb{R}^m$. The nearest point of the column space $K$ to $b$ is $Ax$ with $b - Ax \perp K$, that is $A^{\mathsf T}(b - Ax) = 0$. So $x = (A^{\mathsf T}A)^{-1}A^{\mathsf T}b$, the solution of the normal equations.

**Counterexample (no nearest point in a Banach space).** In $c_0$ with the sup norm, let $f(x) = \sum_{n \ge 1} 2^{-n}x_n$ and $C = \{x : f(x) = 1\}$, a closed convex set. For $x \in C$, $1 = |f(x)| < \|x\|_\infty$, since $|x_n| < \|x\|_\infty$ for all large $n$. But $d(0, C) = 1$: the vector $(1, 1, \dots, 1, 0, \dots)$ with $N$ ones, divided by $1 - 2^{-N}$, is in $C$ with norm $1/(1 - 2^{-N})$. So $C$ has no point nearest to $0$.

### The library around it

Finite dimensional subspaces get `HasOrthogonalProjection` through `ofCompleteSpace`, since a finite dimensional subspace is complete by Chapter 3. The file `Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional` adds the dimension formula `Submodule.finrank_add_finrank_orthogonal` and facts on reflections in finite dimension. The Gram-Schmidt process of Chapter 6 is defined with `starProjection` onto lines.

The dimension formula $\dim K + \dim K^\perp = \dim E$ follows from $E = K \oplus K^\perp$. Its relative form `Submodule.finrank_add_inf_finrank_orthogonal` says $\dim K_1 + \dim(K_1^\perp \cap K_2) = \dim K_2$ for $K_1 \le K_2$, and `Submodule.finrank_orthogonal_span_singleton` says that the orthogonal complement of a nonzero vector in a space of dimension $n + 1$ has dimension $n$. The same file characterizes the orthogonal families of subspaces that span: `OrthogonalFamily.isInternal_iff` says that an orthogonal family of subspaces of a finite dimensional space is an internal direct sum if and only if $\big(\sum_i V_i\big)^\perp = 0$, and `OrthogonalFamily.decomposition` gives the decomposition. The lemma `maximal_orthonormal_iff_basis_of_finiteDimensional` says that a maximal orthonormal set is a basis. Each subspace $K$ of finite dimension is closed, `Submodule.topologicalClosure_eq_self`. For reflections, `Submodule.det_reflection` gives $\det R_K = (-1)^{\dim K^\perp}$, and `LinearIsometryEquiv.reflections_generate_dim` is the theorem of Cartan and Dieudonné: each isometry of a real space of dimension $n$ is a product of at most $n$ reflections in hyperplanes. The proof is an induction on the dimension of the orthogonal complement of the fixed space of the isometry $\varphi$. If $\varphi v = w \ne v$, then the reflection in $(v - w)^\perp$ sends $v$ to $w$ (`Submodule.reflection_sub`), and the reflection composed with $\varphi$ fixes a larger space.

The file `Mathlib.Analysis.InnerProductSpace.Projection.Reflection` defines the reflection in a subspace $K$ with an orthogonal projection, `Submodule.reflection K : E ≃ₗᵢ[𝕜] E`. The formula is $R_K(p) = 2 P_K(p) - p$, the lemma `Submodule.reflection_apply`. It is an involution (`Submodule.reflection_reflection`, `Submodule.reflection_symm`), it fixes exactly the points of $K$ (`Submodule.reflection_eq_self_iff`), it is $-1$ on $K^\perp$, and $R_{K^\perp} = -R_K$ (`Submodule.reflection_orthogonal`). For a line, `Submodule.reflection_singleton_apply` gives $R_{\mathbb{K} u}(v) = 2 \frac{\langle u, v \rangle}{\lVert u \rVert^2} u - v$. An isometry $f$ conjugates reflections: `Submodule.reflection_map`. The same file has `Function.isRadial_iff_comp_linearIsometryEquiv`: a function on a real inner product space depends only on the norm if and only if it is invariant under all linear isometries.

Common errors:

- The projection needs the instance `K.HasOrthogonalProjection`. For a closed subspace of a Hilbert space, state `K` as a `ClosedSubmodule` or provide `CompleteSpace K` with `IsClosed.completeSpace_coe`.
- `orthogonalProjectionOnto` lands in the subtype `K`. Use `starProjection` for an endomorphism of `E`.

### Exercises

1. (A) Compute the projection of $(1, 0, 0)$ onto the plane $x + y + z = 0$ in $\mathbb{R}^3$.
2. (A) Show that $P^2 = P$ and $\langle Pv, w \rangle = \langle v, Pw \rangle$ for an orthogonal projection $P$.
3. (A) Find the nearest point of the closed unit ball of a Hilbert space to a vector $u$ with $\|u\| > 1$.
4. (B) Let $P$ be a bounded operator on a Hilbert space with $P^2 = P$ and $\|P\| \le 1$. Show that $P$ is the orthogonal projection onto its range.
5. (B) Show that the nearest point map onto a closed convex set is Lipschitz with constant $1$.
6. (C) Let $K_1 \subseteq K_2 \subseteq \dots$ be closed subspaces of a Hilbert space with $\bigcup_n K_n$ dense. Show that $P_{K_n}v \to v$ for each $v$.

### Notes and history

The proof of the nearest point theorem by a minimizing sequence uses only the parallelogram law and completeness, so it holds in each complete convex subset of an inner product space, not only in closed subsets of a Hilbert space. The files `Mathlib.Analysis.InnerProductSpace.Projection.Basic`, `Mathlib.Analysis.InnerProductSpace.Projection.Minimal` and `Mathlib.Analysis.InnerProductSpace.Projection.Submodule` have the authors Zhouhang Zhou, Frédéric Dupuis and Heather Macbeth.

### Reference

<?reference?>
