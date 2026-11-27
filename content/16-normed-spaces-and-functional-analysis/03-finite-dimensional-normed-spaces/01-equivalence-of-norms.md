---
title: Equivalence of norms
kind: theory
modules:
  - Mathlib.Analysis.Normed.Module.FiniteDimension
explains:
  E3: [LinearMap.injective_iff_antilipschitz, Module.Basis.opNorm_le, LinearIsometry.toLinearIsometryEquiv]
  E2: [LinearMap.exists_antilipschitzWith, Module.Basis.exists_opNorm_le, Module.Basis.continuous_coe_repr, ContinuousLinearMap.continuous_det, ContinuousLinearMap.isOpen_injective, summable_norm_iff]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Equivalence of norms

### Overview

On $\mathbb{R}^n$ the norms $\|\cdot\|_1$, $\|\cdot\|_2$ and $\|\cdot\|_\infty$ of Chapter 1 satisfy explicit inequalities such as $\|x\|_\infty \le \|x\|_2 \le \sqrt{n}\,\|x\|_\infty$. So they give the same convergent sequences, the same open sets and the same Cauchy sequences. This section proves that the same holds for any two norms on a finite dimensional real or complex vector space. The consequences change the shape of the subject: in finite dimension each linear map is continuous, each normed space is complete, and each subspace of a normed space with finite dimension is closed. None of these facts holds in infinite dimension, as Chapter 2 showed. The section proves the theorem for $\mathbb{R}$ and $\mathbb{C}$ by compactness, and explains the proof of Mathlib, which works over any complete nontrivially normed field.

### Definitions

**Definition (Equivalent norms).** Two norms $\|\cdot\|$ and $\|\cdot\|'$ on a vector space $E$ are *equivalent* if there are constants $a, b > 0$ with
$$a\,\|x\| \le \|x\|' \le b\,\|x\| \quad \text{for all } x \in E.$$

Equivalence of norms is an equivalence relation. Equivalent norms give the same open sets, the same convergent sequences and the same Cauchy sequences, so one of them is complete if and only if the other is. In the language of Chapter 2 the two norms are equivalent if and only if the identity map $(E, \|\cdot\|) \to (E, \|\cdot\|')$ is continuous in both directions.

**Definition (Antilipschitz map).** A map $f : X \to Y$ of metric spaces is *antilipschitz* with constant $K \ge 0$ if $d(x, y) \le K\,d(f(x), f(y))$ for all $x, y$. For a linear map $T$ of normed spaces this says $\|x\| \le K\|Tx\|$. An antilipschitz map is injective, and its inverse on the image is Lipschitz.

::: mathlib
`ContinuousLinearEquiv` · `Mathlib.Topology.Algebra.Module.Equiv.Basic`

`E ≃L[𝕜] F` is a linear equivalence that is continuous in both directions. Mathlib does not state the equivalence of norms as an inequality between two norms on one type, since a type carries one norm instance. Two norms are compared through a continuous linear equivalence between two types, for example a type and a type synonym of it, or through the map `LinearEquiv.toContinuousLinearEquiv` of the next box.

<?decl ContinuousLinearEquiv?>
:::

### Theorems and proofs

**Theorem (Equivalence of norms).** Let $E$ be a finite dimensional vector space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then any two norms on $E$ are equivalent.

*Proof.* Choose a basis $e_1, \dots, e_n$ of $E$ and write $x = \sum_i x_ie_i$. Put $\|x\|_1 = \sum_i |x_i|$, a norm on $E$. Since equivalence is transitive, it suffices to show that any norm $\|\cdot\|$ on $E$ is equivalent to $\|\cdot\|_1$.

Upper bound. With $b = \max_i\|e_i\|$,
$$\|x\| \le \sum_i |x_i|\,\|e_i\| \le b\,\|x\|_1.$$

Lower bound. The upper bound gives $\big|\|x\| - \|y\|\big| \le \|x - y\| \le b\,\|x - y\|_1$, so $x \mapsto \|x\|$ is continuous for the norm $\|\cdot\|_1$. The map $\mathbb{K}^n \to E$, $(x_i) \mapsto \sum x_ie_i$, is a bijective isometry from $(\mathbb{K}^n, \|\cdot\|_1)$ to $(E, \|\cdot\|_1)$. The unit sphere $S = \{x : \|x\|_1 = 1\}$ of $\mathbb{K}^n$ is closed and bounded, so it is compact by the theorem of Heine-Borel (Volume 13, Chapter 5). The continuous function $x \mapsto \|x\|$ attains a minimum $a$ on $S$, at some point $x_0$. Since $\|x_0\|_1 = 1$, $x_0 \neq 0$ and $a = \|x_0\| > 0$. For $x \neq 0$, $x / \|x\|_1 \in S$, so $\|x\| / \|x\|_1 \ge a$, that is, $\|x\| \ge a\,\|x\|_1$. $\square$

The proof uses the compactness of a sphere in $\mathbb{K}^n$, which is a property of $\mathbb{R}$: closed bounded sets are compact. Over the field $\mathbb{Q}$ with the absolute value the theorem fails (see the counterexample below), since $\mathbb{Q}$ is not complete.

**Corollary (Consequences in finite dimension).** Let $E$ be a finite dimensional normed space over $\mathbb{K}$, and $F$ any normed space over $\mathbb{K}$.

1. Each linear map $T : E \to F$ is continuous, with $\|T\| \le \frac{1}{a}\max_i\|Te_i\|$ for the constant $a$ of the proof.
2. $E$ is complete.
3. Each finite dimensional subspace of a normed space is closed.
4. Each linear bijection $E \to E'$ onto another finite dimensional normed space is a homeomorphism.

*Proof.* (1) $\|Tx\| = \|\sum x_iTe_i\| \le \max_i\|Te_i\|\,\|x\|_1 \le \frac1a\max_i\|Te_i\|\,\|x\|$.

(2) Under the isometry with $(\mathbb{K}^n, \|\cdot\|_1)$, a Cauchy sequence in $E$ for $\|\cdot\|$ is Cauchy for $\|\cdot\|_1$ by the lower bound, so each coordinate is a Cauchy sequence in $\mathbb{K}$. Since $\mathbb{K}$ is complete, each coordinate converges, so the sequence converges for $\|\cdot\|_1$, hence for $\|\cdot\|$ by the upper bound.

(3) A finite dimensional subspace $M$ of a normed space $F$ is complete by (2), with the norm of $F$. A complete subspace of a metric space is closed (Volume 13).

(4) The map and its inverse are linear maps from a finite dimensional space, so both are continuous by (1). $\square$

::: mathlib
`LinearMap.continuous_of_finiteDimensional` · `Mathlib.Topology.Algebra.Module.FiniteDimension`

Each linear map from a finite dimensional Hausdorff topological vector space over a complete nontrivially normed field is continuous. The bundled form is `LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F'`, and for equivalences `LinearEquiv.toContinuousLinearEquiv`. Completeness is `FiniteDimensional.completeSpace`, and the closed subspaces are `Submodule.isClosed_of_finiteDimensional`. The older names `FiniteDimensional.complete` and `Submodule.closed_of_finiteDimensional` are deprecated in this edition. All these results live in the topological algebra of Volume 14.

<?decl LinearMap.continuous_of_finiteDimensional?>
:::

**Remark (The proof in Mathlib).** Mathlib proves part (1) of the corollary directly, for a complete nontrivially normed field $\mathbb{K}$ such as $\mathbb{Q}_p$, where the sphere argument fails because closed balls of $\mathbb{K}$ need not be compact. The proof is by induction on the dimension of $E$. In dimension $1$, $E = \mathbb{K}e$ and the map $c \mapsto ce$ is a homeomorphism, by the theorem `unique_topology_of_t2`: a Hausdorff topology on $\mathbb{K}$ that makes it a topological vector space over itself is the norm topology. For the step, a linear functional $f$ on $E$ has a kernel of smaller dimension, which is complete by the induction hypothesis and hence closed. A functional with a closed kernel is continuous (Chapter 2, Section 1). Then a linear map into $F$ is a finite sum of continuous functionals times vectors of $F$.

**Theorem (Injective maps are antilipschitz).** Let $E$ be finite dimensional and $T : E \to F$ linear and injective. Then there is $K > 0$ with $\|x\| \le K\|Tx\|$ for all $x \in E$.

*Proof.* The formula $\|x\|' = \|Tx\|$ defines a norm on $E$: it is a seminorm since $T$ is linear, and $\|x\|' = 0$ gives $Tx = 0$, so $x = 0$ since $T$ is injective. By the theorem, $\|x\| \le K\|x\|'$ for some $K$. $\square$

::: mathlib
`LinearMap.injective_iff_antilipschitz` · `Mathlib.Analysis.Normed.Module.FiniteDimension`

For `f : E →ₗ[𝕜] F` with `[FiniteDimensional 𝕜 E]` and `[CompleteSpace 𝕜]`: `Function.Injective f ↔ ∃ K > 0, AntilipschitzWith K f`. The direction used most is `LinearMap.exists_antilipschitzWith`, from `f.ker = ⊥`. A consequence in the same file is `ContinuousLinearMap.isOpen_injective`: the injective operators form an open set of `E →L[𝕜] F`.

<?decl LinearMap.injective_iff_antilipschitz?>
:::

::: mathlib
`Module.Basis.opNorm_le` · `Mathlib.Analysis.Normed.Module.FiniteDimension`

The bound of part (1) of the corollary, for a basis `v` indexed by a finite type: if `‖u (v i)‖ ≤ M` for each `i`, then `‖u‖ ≤ Fintype.card ι • ‖v.equivFunL‖ * M`. Here `v.equivFunL : E ≃L[𝕜] (ι → 𝕜)` is the continuous equivalence of coordinates, and its norm plays the role of $1/a$ in the proof. The existence form for all `u` at once is `Module.Basis.exists_opNorm_le`. The continuity of each coordinate is `Module.Basis.continuous_coe_repr`.

<?decl Module.Basis.opNorm_le?>
:::

::: mathlib
`LinearIsometry.toLinearIsometryEquiv` · `Mathlib.Analysis.Normed.Module.FiniteDimension`

A linear isometry `E₁ →ₗᵢ[R₁] F` between finite dimensional spaces of the same dimension is surjective, so it is an isometric equivalence. The proof is linear algebra: the map is injective, and an injective linear map between spaces of the same finite dimension is bijective (Volume 7). The right shift of Chapter 2 shows that the statement fails in infinite dimension.

<?decl LinearIsometry.toLinearIsometryEquiv?>
:::

### Examples

**Example (The constants for $\mathbb{R}^n$).** For $x \in \mathbb{R}^n$,
$$\|x\|_\infty \le \|x\|_2 \le \|x\|_1 \le \sqrt{n}\,\|x\|_2 \le n\,\|x\|_\infty.$$
The step $\|x\|_1 \le \sqrt{n}\|x\|_2$ is the inequality of Cauchy-Schwarz for $(|x_i|)$ and $(1, \dots, 1)$. Each constant is sharp: $x = (1, 1, \dots, 1)$ gives $\|x\|_1 = n$, $\|x\|_2 = \sqrt n$, $\|x\|_\infty = 1$, and $x = e_1$ gives equality in the first two inequalities. The constants grow with $n$, which shows why the proof for infinite dimension cannot pass to the limit.

**Example (A norm defined by a matrix).** Let $A$ be an invertible real $n \times n$ matrix and $\|x\|_A = \|Ax\|_2$. Then $\|x\|_A \le \|A\|\,\|x\|_2$ and $\|x\|_2 = \|A^{-1}Ax\|_2 \le \|A^{-1}\|\,\|x\|_A$. So $a = 1/\|A^{-1}\|$ and $b = \|A\|$, with the operator norms for $\|\cdot\|_2$. For $A = \operatorname{diag}(1, \varepsilon)$ with small $\varepsilon > 0$, $a = \varepsilon$ and $b = 1$: two equivalent norms can be far apart.

**Counterexample (Two norms on the polynomials).** On the space $P$ of real polynomials, put $\|p\|_\infty = \max_{[0,1]}|p|$ and $\|p\|_c = \sum_k |a_k|$ for $p = \sum_k a_kt^k$. Then $\|p\|_\infty \le \|p\|_c$. The polynomials $p_n = (1 - t)^n$ have $\|p_n\|_\infty = 1$ and $\|p_n\|_c = \sum_k\binom nk = 2^n$. So no constant $b$ has $\|p\|_c \le b\|p\|_\infty$, and the two norms are not equivalent. The space $P$ has infinite dimension.

**Counterexample (A field that is not complete).** Let $\mathbb{K} = \mathbb{Q}$ with the absolute value and $E = \mathbb{Q}^2$. The formula $\|(x, y)\| = |x + \sqrt2\,y|$ is a norm on $E$: it is a seminorm, and $x + \sqrt2 y = 0$ with $x, y$ rational forces $x = y = 0$. Choose rationals $q_n \to \sqrt 2$ and put $v_n = (q_n, -1)$. Then $\|v_n\| = |q_n - \sqrt2| \to 0$ while $\|v_n\|_\infty \ge 1$. So the norm is not equivalent to $\|\cdot\|_\infty$, and the theorem needs the completeness of the field.

### The library around it

The file `Mathlib.Analysis.Normed.Module.FiniteDimension` has the results of this section that use a norm, and its companion `Mathlib.Topology.Algebra.Module.FiniteDimension` has the results that need only a topology. Further results of the normed file are the continuity of the determinant `ContinuousLinearMap.continuous_det`, the second countability of `E →L[𝕜] F` in finite dimension, the open set of linearly independent families, and `summable_norm_iff`: in a finite dimensional real normed space a series is absolutely summable if and only if it is summable. That last fact is the theorem of Riemann on unconditional sums in $\mathbb{R}^n$, and it fails in infinite dimension by the theorem of Dvoretzky-Rogers. The type class `[FiniteDimensional 𝕜 E]` comes from Volume 7. For the standard spaces Mathlib has the instances, so `ℝ`, `ℂ`, `Fin n → ℝ` and `EuclideanSpace ℝ (Fin n)` are known to be finite dimensional and complete without a proof.

Common errors of a learner:

- Expecting the constants $a$ and $b$ to be independent of the dimension.
- Forgetting that the theorem needs a complete scalar field.
- Expecting instance search to find `CompleteSpace E` for each finite dimensional `E`. For a real space it does, through the instance `FiniteDimensional.proper_real` of Section 2 and the completeness of proper spaces. Over another field `FiniteDimensional.completeSpace` is a theorem, not an instance, and it is applied by hand.

### Exercises

1. (A) Find the best constants $a, b$ with $a\|x\|_1 \le \|x\|_\infty \le b\|x\|_1$ on $\mathbb{R}^n$.
2. (A) Show that equivalence of norms is an equivalence relation, and that equivalent norms have the same Cauchy sequences.
3. (A) Show that $\|(x, y)\| = |x| + 2|y|$ and $\|(x, y)\|' = \max(|x + y|, |x - y|)$ are norms on $\mathbb{R}^2$, and find constants of equivalence.
4. (B) Let $M$ be a subspace of a normed space $E$ with $\dim M < \infty$. Show directly from the theorem that $M$ is closed.
5. (B) Show that the set of invertible $n \times n$ matrices is open and dense in the space of all matrices, with any norm.
6. (B) On $C[0,1]$ show that $\|f\|_\infty$ and $\|f\|_1 = \int_0^1|f|$ are not equivalent, and that $(C[0,1], \|\cdot\|_1)$ is not complete.
7. (C) Let $E$ be finite dimensional and $F$ any normed space. Show that the injective operators form an open subset of $L(E, F)$. Hint: if $\|x\| \le K\|Tx\|$ and $\|S - T\| < 1/K$, then $S$ is injective.
8. (C) Let $E$ be a normed space of infinite dimension. Show that $E$ has a norm that is not equivalent to the given one. Hint: use a discontinuous functional $f$ of Chapter 2 and $\|x\|' = \|x\| + |f(x)|$.

### Notes and history

The equivalence of all norms on a finite dimensional space is a classical consequence of the compactness of spheres in $\mathbb{R}^n$, and the compactness criterion of the next section is due to F. Riesz. The counterexample over $\mathbb{Q}$ shows that the completeness of the field is the essential hypothesis, and the induction on the dimension that Mathlib uses avoids the compactness of spheres. The file `Mathlib.Analysis.Normed.Module.FiniteDimension` has the author Sébastien Gouëzel, and the file `Mathlib.Topology.Algebra.Module.FiniteDimension` has the authors Sébastien Gouëzel and Anatole Dedecker.

### Reference

<?reference?>
