---
title: Unbounded operators and reproducing kernels
kind: api
modules:
  - Mathlib.Analysis.InnerProductSpace.LinearPMap
  - Mathlib.Analysis.InnerProductSpace.Reproducing
  - Mathlib.Analysis.InnerProductSpace.Reproducing.Operations
  - Mathlib.Analysis.InnerProductSpace.StandardSubspace
explains:
  E2: [LinearPMap.adjoint, LinearPMap.IsFormalAdjoint.le_adjoint, LinearPMap.adjoint_isClosed, RKHS, RKHS.kerFun, RKHS.kernel, RKHS.OfKernel, RKHS.mem_topologicalClosure_span_kerFun, "RKHS.Add'.kernel_sum_eq_sum_of_kernel", StandardSubspace.symplComp]
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

## Unbounded operators and reproducing kernels

### Overview

Sections 2 and 3 use the Riesz representation theorem to make the adjoint of a bounded operator. This section uses the same theorem in three other places. The first is the adjoint of a linear map that is defined only on a subspace, such as a differential operator on $L^2$. The second is a Hilbert space of functions in which each evaluation $f \mapsto f(x)$ is continuous. Riesz then gives a vector $k_x$ with $f(x) = \langle k_x, f \rangle$, and the function $K(x, y) = \langle k_x, k_y \rangle$ is the reproducing kernel. The third is the standard subspaces of a complex Hilbert space, which come from the theory of von Neumann algebras.

A partial linear map from $E$ to $F$ is a linear map $T$ from a submodule $\operatorname{dom} T$ of $E$ to $F$. Its adjoint $T^*$ has as domain the set of $y \in F$ such that $x \mapsto \langle y, T x \rangle$ is continuous on $\operatorname{dom} T$. For such $y$, Riesz extends this functional to the closure of the domain and gives a vector $T^* y$. When the domain is dense, $T^*$ is the largest map $S$ with $\langle S y, x \rangle = \langle y, T x \rangle$ for all $x \in \operatorname{dom} T$ and $y \in \operatorname{dom} S$, and its graph is closed. A self-adjoint partial map is one with $T^* = T$. Such a map is closed and densely defined.

A reproducing kernel Hilbert space, or RKHS, is a Hilbert space $H$ of functions $X \to V$, where $V$ is a Hilbert space too, such that the inclusion of $H$ in $X \to V$ is a continuous linear map. The kernel is then a matrix $K$ indexed by $X \times X$ with entries in the bounded operators on $V$. It is positive semidefinite. The theorem of Moore gives the converse: each positive semidefinite kernel is the kernel of exactly one RKHS, up to isometry.

### The library around it

The file `Mathlib.Analysis.InnerProductSpace.LinearPMap` works with the type `E →ₗ.[𝕜] F` of partial linear maps from the linear algebra library, with `E` and `F` inner product spaces. The predicate `LinearPMap.IsFormalAdjoint T S` says that $\langle T x, y \rangle = \langle x, S y \rangle$ for all $x$ in the domain of $T$ and $y$ in the domain of $S$. The definition `LinearPMap.adjoint T` needs `CompleteSpace E`. The lemma `LinearPMap.mem_adjoint_domain_iff` says that `y` is in the domain of the adjoint if and only if the map $x \mapsto \langle y, T x \rangle$ is continuous.

The main facts all assume that the domain of `T` is dense. Under this hypothesis, `LinearPMap.adjoint_isFormalAdjoint` says that the adjoint is a formal adjoint, and `LinearPMap.IsFormalAdjoint.le_adjoint` says that each formal adjoint `S` satisfies `S ≤ T.adjoint`. So the adjoint is the largest formal adjoint, in the order of extension on partial maps. The lemma `LinearPMap.adjoint_isClosed` says that the adjoint is closed, with `LinearPMap.IsClosed` from the topology library. If the domain is not dense, the definition still gives a value, but `LinearPMap.adjoint_apply_of_not_dense` says that this value is zero. This is a junk value, and a statement about it is not a statement about an adjoint in the usual sense.

The graph view is also available. For a submodule `g` of `E × F`, `Submodule.adjoint g` is a submodule of `F × E`, and `Submodule.mem_adjoint_iff` describes it with the condition $\langle b, x_1 \rangle - \langle a, x_2 \rangle = 0$ for all $(a, b) \in g$. Then `LinearPMap.adjoint_graph_eq_graph_adjoint` says that, for a dense domain, the graph of `T.adjoint` is the adjoint of the graph of `T`. The instance `LinearPMap.instStar` makes the adjoint the `star` of a map from `E` to `E`, and `IsSelfAdjoint T` then means `star T = T`, as `LinearPMap.isSelfAdjoint_def` says. The lemmas `IsSelfAdjoint.isClosed` and `IsSelfAdjoint.dense_domain` give the two properties of a self-adjoint map. For a bounded map, `ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense` says that the restriction of `A` to a dense submodule has as adjoint the bounded adjoint of `A`, defined on all of `F`.

The class `RKHS 𝕜 H X V` in `Mathlib.Analysis.InnerProductSpace.Reproducing` holds one field, a continuous linear map `RKHS.coeCLM 𝕜` from `H` to the space `X → V` with the product topology, and the proof that this map is injective. So an element of `H` is a function, and `RKHS.ext` says that two elements are equal when they agree at each point. The lemmas `RKHS.coe_add`, `RKHS.coe_smul` and their variants push the algebra to the functions. The map `RKHS.eval H x` is the evaluation at `x`, as a continuous linear map `H →L[𝕜] V`, and `RKHS.continuous_eval_const` says that each evaluation is continuous.

When `H` and `V` are complete, `RKHS.kerFun H x` is the map `V →L[𝕜] H` that is the adjoint of `RKHS.eval H x`, as `RKHS.kerFun_eq_adjoint_eval` says. The reproducing property is `RKHS.inner_kerFun`: the inner product of `f` with `RKHS.kerFun H x v` is the inner product of `f x` with `v`. The kernel `RKHS.kernel H` is the matrix whose entry at $(x, y)$ is $k_x^* k_y$, the adjoint of `RKHS.kerFun H x` composed with `RKHS.kerFun H y`, and `RKHS.kernel_inner` expresses it with inner products. The lemmas `RKHS.posSemidef_kernel` and `RKHS.isHermitian_kernel` give its two basic properties, and `RKHS.posSemidef_iff_re_sum_kernel` translates positive semidefinite into a sum condition over finitely supported families. The norm estimates are `RKHS.norm_apply_le`, which says that `‖f x‖ ≤ ‖f‖ * √‖RKHS.kernel H x x‖`, `RKHS.norm_kernel_le` and `RKHS.norm_kerFun_sub_kerFun`. The lemma `RKHS.tendstoUniformly_of_norm_kerFun_le` uses the first estimate: if the kernel is bounded on the diagonal, then convergence in `H` implies uniform convergence of the functions.

The span of the vectors `RKHS.kerFun H x v` is dense, which is `RKHS.kerFun_dense`. A function orthogonal to all of them is zero at the points, which is `RKHS.apply_eq_zero_of_mem_orthogonal_span_kerFun`. The representer theorem `RKHS.mem_topologicalClosure_span_kerFun` uses this fact. Take points $x_1, \dots, x_n$, a loss `L` of the values at these points, and a monotone penalty `Ω` on the norm. A minimizer `f` of `L (f x_1, ..., f x_n) + Ω ‖f‖` then lies in the closed span of the vectors `RKHS.kerFun H (x i) v`. The proof writes `f` as `p + q` with `p` in the closed span and `q` orthogonal to it. Then `q` vanishes at each point, so the loss of `p` equals the loss of `f`, and `‖p‖ ≤ ‖f‖`.

For the converse direction, `RKHS.OfKernel K` is the RKHS of a kernel `K` with a `Fact K.PosSemidef` instance, and `RKHS.OfKernel.kernel_ofKernel` says that its kernel is `K`. The definition `RKHS.equiv` gives a linear isometry between two spaces with the same kernel, which is the uniqueness part of the Moore theorem. The rank one kernel `RKHS.outerKernel 𝕜 f` of a function `f : X → V` is positive semidefinite by `RKHS.posSemidef_outerKernel`, and `RKHS.kernel_span_singleton` identifies it, after a scale, with the kernel of the line spanned by `f`. For a closed submodule `H₀` of `H`, the lemmas `RKHS.kerFun_submodule` and `RKHS.kernel_submodule` compute the kernel of `H₀` with the orthogonal projection onto `H₀`. The lemma `RKHS.continuous_kernel_tfae` gives three equivalent conditions on a topological space `X`: the kernel is continuous, the map `RKHS.kerFun H` is continuous, and the evaluation map is continuous.

The file `Mathlib.Analysis.InnerProductSpace.Reproducing.Operations` adds the sum of two kernels. The type `RKHS.Add'.sumSpace H H'` is the space of functions `f₁ + f₂` with `f₁ ∈ H` and `f₂ ∈ H'`. It is the quotient of `WithLp 2 (H × H')` by the kernel of the map `RKHS.Add'.generator`, with the quotient norm. The lemma `RKHS.Add'.kernel_sum_eq_sum_of_kernel` says that its kernel is `RKHS.kernel H + RKHS.kernel H'`. The norm is the smallest value of `‖f₁‖ ^ 2 + ‖f₂‖ ^ 2`, which is the content of `RKHS.Add'.norm_sq_le` and `RKHS.Add'.exists_eq_add_and_norm_sq_eq_add`. The isometry `RKHS.Add'.OfKernelAddEquiv` identifies the RKHS of `K + K'` with the sum space.

The file `Mathlib.Analysis.InnerProductSpace.StandardSubspace` works in a complex Hilbert space `H`, seen also as a real space with the inner product `ClosedSubmodule.instInnerProductSpaceReal`, whose value is the real part of the complex one by `ClosedSubmodule.inner_real_eq_re_inner`. For a closed real subspace `S`, `ClosedSubmodule.mulI S` is the subspace $i S$, and `ClosedSubmodule.symplComp S` is the symplectic complement, the set of `x` with $\operatorname{Im} \langle y, x \rangle = 0$ for all $y \in S$, as `ClosedSubmodule.mem_symplComp_iff` says. The lemma `ClosedSubmodule.mulI_orthogonal_eq_symplComp` says that the symplectic complement is $i$ times the real orthogonal complement. A `StandardSubspace H` is a closed real subspace `S` that is cyclic, `S ⊔ i S = ⊤`, and separating, `S ⊓ i S = ⊥`. These are the fields `StandardSubspace.IsCyclic` and `StandardSubspace.IsSeparating`. In a complete space, `StandardSubspace.symplComp` gives the symplectic complement of a standard subspace as a standard subspace, and `StandardSubspace.symplComp_symplComp_eq` says that the operation is an involution. The equivalence `scalarSMulCLE H c` is the real linear equivalence $x \mapsto c x$ for a unit `c` of `ℂ`, and `Complex.UnitI` is `Complex.I` as a unit.

#### Common errors

1. A lemma on `LinearPMap.adjoint` without the hypothesis `Dense (T.domain : Set E)` does not exist for the main facts. If the domain is not dense, the adjoint is the zero map on its domain, so prove the density first.
2. The kernel `RKHS.kernel H` has values in `V →L[𝕜] V`, not in `𝕜`. For scalar valued functions, take `V = 𝕜`, and an entry is then a bounded operator on `𝕜`, not a number.
3. The inner product of a complex space and the real inner product from `ClosedSubmodule.instInnerProductSpaceReal` are two different instances on the same type. The real one is a `def`, not a global instance, so activate it with a local instance before a real statement.

### Exercises

1. (A) Use `RKHS.inner_kerFun` and the Cauchy Schwarz inequality to prove `‖f x‖ ≤ ‖f‖ * ‖RKHS.kerFun H x‖`.
2. (A) Prove that a self-adjoint partial map `A` with `A.domain = ⊤` comes from a bounded symmetric operator, with the closed graph theorem.
3. (B) Show that if `T.IsFormalAdjoint S` and the domain of `S` is dense, then `T ≤ S.adjoint`, with `LinearPMap.IsFormalAdjoint.le_adjoint`.
4. (B) Prove the representer theorem `RKHS.mem_topologicalClosure_span_kerFun` in the case of one point $x_1$ and `V = 𝕜`.
5. (B) Compute `RKHS.kernel` for the line `𝕜 ∙ f` and compare it with `RKHS.kernel_span_singleton`.
6. (C) Prove that `S.symplComp` is separating when `S` is cyclic, with `ClosedSubmodule.mulI_orthogonal_eq_symplComp`.

### Reference

<?reference?>
