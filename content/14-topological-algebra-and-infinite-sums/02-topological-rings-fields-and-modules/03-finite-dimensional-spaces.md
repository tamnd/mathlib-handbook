---
title: Finite-dimensional topological vector spaces
kind: theory
modules:
  - Mathlib.Topology.Algebra.Module.FiniteDimension
  - Mathlib.Topology.Algebra.Module.ModuleTopology
  - Mathlib.Topology.Instances.RealVectorSpace
explains:
  E3: [LinearMap.continuous_of_finiteDimensional, FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq, LinearMap.continuous_iff_isClosed_ker]
  E2: [unique_topology_of_t2, Submodule.isClosed_of_finiteDimensional, Submodule.isComplete_of_finiteDimensional, FiniteDimensional.completeSpace, LinearMap.toContinuousLinearMap, continuous_equivFun_basis, LinearMap.continuous_of_isClosed_ker, LinearMap.continuous_of_ne_zero_on_open, LinearEquiv.toContinuousLinearEquiv, FiniteDimensional.of_locallyCompactSpace, isModuleTopologyOfFiniteDimensional, IsModuleTopology, moduleTopology, IsModuleTopology.continuous_of_linearMap, map_real_smul, AddMonoidHom.toRealLinearMap]
  E1: auto
families: []
requires: [V07, V13.C02, V13.C04, V13.C07, V14.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finite-dimensional topological vector spaces

### Overview

On $\mathbb{R}^n$ all norms are equivalent. This section proves a stronger statement: a finite-dimensional vector space $E$ over a complete nontrivially normed field $\Bbbk$ has only one Hausdorff topology that makes it a topological vector space. So each linear map out of $E$ is continuous, each finite-dimensional subspace of a Hausdorff topological vector space is closed, and two such spaces of the same dimension are isomorphic as topological vector spaces. The proof is an induction on the dimension, through the criterion that a linear functional is continuous if and only if its kernel is closed. Two counterexamples show that the Hausdorff property and the completeness of $\Bbbk$ are both needed.

Throughout, $\Bbbk$ is a nontrivially normed field: a field with an absolute value $|\cdot|$ for which some $c \in \Bbbk$ has $0 < |c| \ne 1$. Then $|c^n|$ or $|c^{-n}|$ tends to $0$, so $\Bbbk$ has nonzero elements of arbitrarily small absolute value. The fields $\mathbb{R}$, $\mathbb{C}$, $\mathbb{Q}$ and $\mathbb{Q}_p$ are examples, and the first two and the last are complete.

### Definitions

**Definition (Balanced set).** A subset $V$ of a vector space over $\Bbbk$ is balanced if $aV \subseteq V$ for each $a \in \Bbbk$ with $|a| \le 1$.

**Definition (Finite-dimensional topological vector space).** A finite-dimensional topological vector space over $\Bbbk$ is a topological vector space $E$ over $\Bbbk$, in the sense of Section 2, whose dimension $\dim_\Bbbk E$ is finite.

### Theorems and proofs

**Lemma (Balanced neighbourhoods).** In a topological vector space over $\Bbbk$, each neighbourhood $W$ of $0$ contains a balanced neighbourhood of $0$.

*Proof.* The scalar multiplication is continuous at $(0, 0)$ and $0 \cdot 0 = 0$. So there are $\delta > 0$ and a neighbourhood $U$ of $0$ with $cU \subseteq W$ whenever $|c| < \delta$. Let $V = \bigcup_{0 < |c| < \delta} cU$. Then $V \subseteq W$. Choose $c_0$ with $0 < |c_0| < \delta$. For $c \ne 0$, the map $x \mapsto cx$ is a homeomorphism with inverse $x \mapsto c^{-1}x$, so $c_0 U$ is a neighbourhood of $0$, and so is $V$. For $|a| \le 1$ and $0 < |c| < \delta$, either $a = 0$ and $a(cU) = \{0\} \subseteq V$, or $0 < |ac| < \delta$ and $a(cU) = (ac)U \subseteq V$. $\square$

**Theorem (Closed kernels).** Let $E$ be a topological vector space over $\Bbbk$ and $\ell : E \to \Bbbk$ a linear functional. Then $\ell$ is continuous if and only if $\ker \ell$ is closed.

*Proof.* If $\ell$ is continuous, $\ker \ell = \ell^{-1}(\{0\})$ is closed. Conversely let $\ker \ell$ be closed and $\ell \ne 0$. Choose $x_0$ with $\ell(x_0) = 1$. The set $A = \ell^{-1}(1) = x_0 + \ker \ell$ is closed, as a translate of a closed set, and $0 \notin A$. So $E \setminus A$ is a neighbourhood of $0$, and by the lemma it contains a balanced neighbourhood $V$ of $0$. Then $|\ell(v)| < 1$ for $v \in V$: if $|\ell(v)| \ge 1$, then $a = \ell(v)^{-1}$ has $|a| \le 1$, so $av \in V$, and $\ell(av) = 1$, which contradicts $V \cap A = \emptyset$. Now let $\varepsilon > 0$ and choose $c \in \Bbbk$ with $0 < |c| < \varepsilon$. The set $cV$ is a neighbourhood of $0$, and $|\ell(cv)| = |c||\ell(v)| < \varepsilon$ for $v \in V$. So $\ell$ is continuous at $0$, and by Section 2 it is continuous. $\square$

The proof does not use the completeness of $\Bbbk$ or the dimension of $E$.

::: mathlib
`LinearMap.continuous_iff_isClosed_ker` · `Mathlib.Topology.Algebra.Module.FiniteDimension`

For `l : E →ₗ[𝕜] 𝕜` with `[NontriviallyNormedField 𝕜] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]`: `Continuous l ↔ IsClosed (ker l)`. The direction used in the induction is `LinearMap.continuous_of_isClosed_ker`. A variant, `LinearMap.continuous_of_ne_zero_on_open`, needs only a nonempty open set on which `l` has no zero.

<?decl LinearMap.continuous_iff_isClosed_ker?>
:::

**Lemma (Subspaces that look like $\Bbbk^m$ are closed).** Let $\Bbbk$ be complete and $E$ a Hausdorff topological vector space over $\Bbbk$. Let $F \le E$ be a subspace and $\psi : \Bbbk^m \to F$ a linear bijection that is a homeomorphism for the subspace topology on $F$. Then $F$ is closed in $E$.

*Proof.* Let $x \in \overline{F}$. The sets $(x + U) \cap F$, for $U$ a neighbourhood of $0$ in $E$, are nonempty and form a filter base $\mathcal{G}$ on $F$. Give $\Bbbk^m$ the norm $\|y\| = \max_i |y_i|$. The filter $\psi^{-1}(\mathcal{G})$ is Cauchy for this norm. Indeed, let $W$ be a ball around $0$ in $\Bbbk^m$. Since $\psi$ is a homeomorphism onto $F$, there is an open $U \ni 0$ in $E$ with $\psi(W) \supseteq U \cap F$. Choose $U'$ with $U' - U' \subseteq U$. For $a, b \in (x + U') \cap F$, $a - b \in U \cap F \subseteq \psi(W)$, so $\psi^{-1}(a) - \psi^{-1}(b) \in W$. The space $\Bbbk^m$ is complete because $\Bbbk$ is, so $\psi^{-1}(\mathcal{G})$ converges to some $y$ (Volume 13, Chapter 7). Since $\psi$ is continuous, $\mathcal{G}$ converges to $\psi(y)$ in $E$. But $\mathcal{G}$ also converges to $x$. Limits are unique in a Hausdorff space, so $x = \psi(y) \in F$. $\square$

**Theorem (Uniqueness of the topology).** Let $\Bbbk$ be complete and $E$ a Hausdorff topological vector space over $\Bbbk$ of finite dimension $n$. Then each linear bijection $\varphi : \Bbbk^n \to E$ is a homeomorphism.

*Proof.* By induction on $n$. For $n = 0$ both spaces are a point. Let $n \ge 1$ and assume the theorem for dimension $n - 1$. By Section 2, $\varphi$ is continuous. Let $\ell : E \to \Bbbk$ be a nonzero linear functional. Its kernel $K$ has dimension $n - 1$, and it is a Hausdorff topological vector space with the subspace topology. By the hypothesis of induction, a linear bijection $\Bbbk^{n-1} \to K$ is a homeomorphism. By the lemma on subspaces, $K$ is closed in $E$, and by the theorem on closed kernels, $\ell$ is continuous. So each linear functional on $E$ is continuous. The coordinates of $\varphi^{-1}$ are linear functionals, so $\varphi^{-1} : E \to \Bbbk^n$ is continuous. $\square$

**Corollary.** Let $\Bbbk$ be complete and $E$ a finite-dimensional Hausdorff topological vector space over $\Bbbk$. (a) Each linear map from $E$ to a topological vector space is continuous. (b) Two such spaces of the same dimension are isomorphic as topological vector spaces. (c) A finite-dimensional subspace of a Hausdorff topological vector space is closed.

*Proof.* (a) Write $f = (f \circ \varphi) \circ \varphi^{-1}$. The map $f \circ \varphi$ is continuous by Section 2 and $\varphi^{-1}$ by the theorem. (b) Compose two homeomorphisms $\Bbbk^n \to E$ and $\Bbbk^n \to E'$. (c) Apply the theorem to the subspace and then the lemma on subspaces. $\square$

::: mathlib
`LinearMap.continuous_of_finiteDimensional` · `Mathlib.Topology.Algebra.Module.FiniteDimension`

Part (a), for `f : E →ₗ[𝕜] F'` under `[CompleteSpace 𝕜] [T2Space E] [FiniteDimensional 𝕜 E]`. The target needs no Hausdorff property. The bundled form `LinearMap.toContinuousLinearMap` is a linear equivalence `(E →ₗ[𝕜] F') ≃ₗ[𝕜] (E →L[𝕜] F')`. For a basis `ξ`, `continuous_equivFun_basis` gives the continuity of the coordinates.

<?decl LinearMap.continuous_of_finiteDimensional?>
:::

::: mathlib
`FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq` · `Mathlib.Topology.Algebra.Module.FiniteDimension`

Part (b): from `finrank 𝕜 E = finrank 𝕜 F` it gives `Nonempty (E ≃L[𝕜] F)`, with `T2Space` on both sides. `LinearEquiv.toContinuousLinearEquiv` upgrades a given linear equivalence. Part (c) is `Submodule.isClosed_of_finiteDimensional`. With a uniform structure, as in Chapter 3, `FiniteDimensional.completeSpace` and `Submodule.isComplete_of_finiteDimensional` state completeness. The older names `Submodule.closed_of_finiteDimensional` and `FiniteDimensional.complete` are deprecated.

<?decl FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq?>
:::

**Proposition (Additive maps of real spaces).** Let $E, F$ be topological vector spaces over $\mathbb{R}$, $F$ Hausdorff, and $f : E \to F$ a continuous additive map. Then $f$ is $\mathbb{R}$-linear.

*Proof.* Additivity gives $f(nx) = nf(x)$ for $n \in \mathbb{Z}$, and then $m f(x/m) = f(x)$ gives $f(qx) = qf(x)$ for $q \in \mathbb{Q}$. Fix $x$. The maps $c \mapsto f(cx)$ and $c \mapsto cf(x)$ from $\mathbb{R}$ to $F$ are continuous and agree on the dense set $\mathbb{Q}$. Two continuous maps into a Hausdorff space that agree on a dense set are equal. $\square$

This is `map_real_smul`, and `AddMonoidHom.toRealLinearMap` gives the continuous linear map.

### Examples

**Example (Norms on $\mathbb{R}^2$).** Let $\|x\|_1 = |x_1| + |x_2|$ and $\|x\|_\infty = \max(|x_1|, |x_2|)$. Then $\|x\|_\infty \le \|x\|_1 \le 2\|x\|_\infty$, so the two norms give the same topology. The theorem says more: each Hausdorff vector space topology on $\mathbb{R}^2$ is this one, for example the topology of the norm $\|x\| = |x_1 + 3x_2| + |x_2|$, which comes from the linear bijection $(x_1, x_2) \mapsto (x_1 + 3x_2, x_2)$.

**Example (Polynomials of degree at most $1$).** Let $P_1$ be the real polynomials $p = a + bx$, with $\|p\| = \sup_{[0,1]} |p|$. The functional $p \mapsto b = p'(0)$ is continuous by the corollary. A bound comes from $b = p(1) - p(0)$: $|b| \le 2\|p\|$. Compare the counterexample of Section 2, where differentiation on all polynomials is not continuous.

**Counterexample (The Hausdorff property).** Give $\mathbb{R}^2$ the topology whose open sets are $U \times \mathbb{R}$ with $U \subseteq \mathbb{R}$ open. Addition and scalar multiplication are continuous, because the topology is induced by the linear map $(x_1, x_2) \mapsto x_1$. The functional $\ell(x) = x_2$ is not continuous: $\ell^{-1}((0, 1))$ is $\mathbb{R} \times (0, 1)$, which is not open. The space is not Hausdorff, and its kernel $\ker \ell = \mathbb{R} \times \{0\}$ is not closed: its closure is $\mathbb{R}^2$.

**Counterexample (The completeness of the field).** Let $\Bbbk = \mathbb{Q}$ and $E = \mathbb{Q}(\sqrt 2) = \{a + b\sqrt 2 : a, b \in \mathbb{Q}\} \subseteq \mathbb{R}$, with the subspace topology. It is a Hausdorff topological vector space over $\mathbb{Q}$ of dimension $2$. The functional $\ell(a + b\sqrt 2) = b$ is not continuous. Choose rationals $a_n \to -\sqrt 2$, and let $x_n = a_n + \sqrt 2$. Then $x_n \to 0$ in $E$, but $\ell(x_n) = 1$ for all $n$. So $E$ is not homeomorphic to $\mathbb{Q}^2$ by a linear map, and the lemma on subspaces fails: the line $\mathbb{Q} \subseteq E$ is dense in $E$, not closed.

**Remark (Common errors).** A learner often applies the theorem with no Hausdorff hypothesis, or over $\mathbb{Q}$. A second error is to think that the theorem needs a norm on $E$. It does not: $E$ is any topological vector space, and the norm appears only on $\Bbbk^n$. A third error, in Lean, is to call `LinearMap.continuous_of_finiteDimensional` when the instance `FiniteDimensional 𝕜 E` is missing.

::: mathlib
`IsModuleTopology` · `Mathlib.Topology.Algebra.Module.ModuleTopology`

`IsModuleTopology R A` states that the topology on `A` is `moduleTopology R A`, the finest topology that makes addition and scalar multiplication continuous. For such a module each linear map to a topological module is continuous, `IsModuleTopology.continuous_of_linearMap`. The theorem `isModuleTopologyOfFiniteDimensional` states that a finite-dimensional Hausdorff space over a complete field has this property. The definition makes sense over any topological ring.

<?decl IsModuleTopology?>
:::

### The library around it

All results of the section are in `Mathlib.Topology.Algebra.Module.FiniteDimension`, stated for a `NontriviallyNormedField 𝕜`. The norm of `𝕜` is needed for the balanced neighbourhoods and for the completeness of `𝕜^n`. The module `Mathlib.Topology.Algebra.Module.ModuleTopology` gives the other approach through `IsModuleTopology`, and `Mathlib.Topology.Instances.RealVectorSpace` holds the result on additive maps of real spaces. The only Hausdorff topology on `𝕜` that makes it a topological vector space over itself is the norm topology, `unique_topology_of_t2`.

### Exercises

1. (A) Show that on $\mathbb{C}^n$ the norms $\|z\|_1$, $\|z\|_2$ and $\|z\|_\infty$ give the same topology, with explicit constants.
2. (A) Show that a finite-dimensional subspace of $C[0,1]$ is closed for the norm $\|\cdot\|_\infty$.
3. (A) Let $E$ be a Hausdorff topological vector space over $\mathbb{R}$ of finite dimension. Show that $E$ is locally compact. *Hint:* $\mathbb{R}^n$ is.
4. (B) Let $P_d$ be the real polynomials of degree at most $d$, with $\|p\| = \sup_{[0,1]} |p|$. Show that there is a constant $C_d$ with $|p'(0)| \le C_d\|p\|$, and that no constant works for all $d$.
5. (A) Show that each balanced set $V$ with $0 \in V$ satisfies $cV = V$ for $|c| = 1$.
6. (B) Let $\Bbbk$ be complete and $E$ a Hausdorff topological vector space over $\Bbbk$. Let $F \le E$ be closed and $G \le E$ finite-dimensional. Show that $F + G$ is closed. *Hint:* pass to $E/F$, which is Hausdorff by Section 2.
7. (C) Let $E = \mathbb{Q}(\sqrt 2)$ as in the counterexample. Show that each nonzero $\mathbb{Q}$-linear functional on $E$ is discontinuous. *Hint:* a continuous one is uniformly continuous, so it extends to a continuous additive map $\mathbb{R} \to \mathbb{R}$, which is $\mathbb{R}$-linear by the proposition on additive maps.

### Notes and history

The uniqueness of the topology of a finite-dimensional Hausdorff topological vector space over $\mathbb{R}$ or $\mathbb{C}$ is due to Tychonoff, in his paper of 1935 on fixed points. The theorem of Riesz, in its general form, states that a locally compact Hausdorff topological vector space over a complete nontrivially normed field is finite-dimensional; Mathlib has it as `FiniteDimensional.of_locallyCompactSpace`. With the axiom of choice, a basis of $\mathbb{R}$ over $\mathbb{Q}$ gives a discontinuous additive map $\mathbb{R} \to \mathbb{R}$.

### Reference

<?reference?>
