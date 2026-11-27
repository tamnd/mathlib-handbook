---
title: Smooth bump functions
kind: theory
modules:
  - Mathlib.Geometry.Manifold.BumpFunction
explains:
  E3: [SmoothBumpFunction, SmoothBumpFunction.contMDiff, SmoothBumpFunction.nhds_basis_tsupport]
  E2: [SmoothBumpFunction.closedBall_subset, SmoothBumpFunction.coe_def, SmoothBumpFunction.rOut_pos, SmoothBumpFunction.eqOn_source, SmoothBumpFunction.one_of_dist_le, SmoothBumpFunction.support_eq_inter_preimage, SmoothBumpFunction.support_eq_symm_image, SmoothBumpFunction.support_subset_source, SmoothBumpFunction.image_eq_inter_preimage_of_subset_support, SmoothBumpFunction.mem_Icc, SmoothBumpFunction.nonneg, SmoothBumpFunction.le_one, SmoothBumpFunction.eventuallyEq_one, SmoothBumpFunction.c_mem_support, SmoothBumpFunction.tsupport_mem_nhds, SmoothBumpFunction.isCompact_symm_image_closedBall, SmoothBumpFunction.isClosed_symm_image_closedBall, SmoothBumpFunction.tsupport_subset_chartAt_source, SmoothBumpFunction.hasCompactSupport, SmoothBumpFunction.nhds_basis_support, SmoothBumpFunction.exists_r_pos_lt_subset_ball, SmoothBumpFunction.updateRIn, SmoothBumpFunction.instNonempty, SmoothBumpFunction.contMDiffAt, SmoothBumpFunction.continuous, SmoothBumpFunction.contMDiff_smul]
  E1: auto
families: []
requires: [V23.C02, V23.C03, V13.C04, V13.C05, V17.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Smooth bump functions

### Overview

A bump function at a point $c$ of a manifold is a smooth function with values in $[0, 1]$ that is $1$ near $c$ and $0$ outside a small neighbourhood of $c$. On a normed space, Volume 17, Chapter 4 builds such functions on balls. On a manifold, Mathlib moves them from the model space with the extended chart at $c$.

This section defines smooth bump functions, computes their supports, and proves that they are smooth when the manifold is Hausdorff and of class $C^\infty$. It proves that the closures of their supports are compact and form a basis of neighbourhoods of $c$. These facts are the input of the partitions of unity of Section 2. The example of the line with two origins shows that the Hausdorff condition cannot be dropped.

### Definitions

Let $E$ be a finite dimensional real normed space, $I : H \to E$ a model with corners, and $M$ a manifold modelled on $I$. For $c \in M$ write $\hat\varphi = \hat\varphi_c$ for the extended chart at $c$ of Chapter 2, Section 2, with source $\mathrm{dom}\,\varphi$ and target $T \subseteq \mathrm{range}\, I$, and write $\hat c = \hat\varphi(c)$.

**Definition (Bump function of the model space).** For $0 < r < R$ a bump function $\beta : E \to [0, 1]$ for $(\hat c, r, R)$ is a $C^\infty$ map with $\beta = 1$ on the closed ball $\bar B(\hat c, r)$ and $\{\beta \neq 0\} = B(\hat c, R)$. Volume 17, Chapter 4 constructs one for every finite dimensional space.

**Definition (Smooth bump function).** A smooth bump function at $c$ consists of radii $0 < r < R$ such that
$$\bar B(\hat c, R) \cap \mathrm{range}\, I \subseteq T.$$
Its function is $f : M \to \mathbb{R}$ with $f(x) = \beta(\hat\varphi(x))$ for $x \in \mathrm{dom}\,\varphi$ and $f(x) = 0$ otherwise, where $\beta$ is the bump function of the model space for $(\hat c, r, R)$.

**Definition (Support).** The support of $f$ is $\mathrm{supp}\, f = \{x \mid f(x) \neq 0\}$, and its closure $\overline{\mathrm{supp}}\, f$ is the topological support.

The condition on $R$ asks that the closed ball, seen inside the range of $I$, lies in the domain of $\hat\varphi^{-1}$. At a boundary point $c$, the ball meets the complement of $\mathrm{range}\, I$, and only the part inside $\mathrm{range}\, I$ matters.

::: mathlib
`SmoothBumpFunction` · `Mathlib.Geometry.Manifold.BumpFunction`

`SmoothBumpFunction I c` extends `ContDiffBump (extChartAt I c c)`, which holds the radii `rIn` and `rOut`. Its one new field is `closedBall_subset`. The coercion to a function is `SmoothBumpFunction.coe_def`: the indicator of `(chartAt H c).source` of the composite of the bump function with `extChartAt I c`. The lemmas need `FiniteDimensional ℝ E`, and the topological ones need `T2Space M`.

<?decl SmoothBumpFunction?>
<?decl SmoothBumpFunction.coe_def?>
<?decl SmoothBumpFunction.closedBall_subset?>
:::

### Theorems and proofs

Fix a smooth bump function $f$ at $c$ with radii $r < R$.

**Theorem (Existence).** For every $R_0 > 0$ there is a smooth bump function at $c$ with $R \le R_0$.

*Proof.* The target $T$ is a neighbourhood of $\hat c$ within $\mathrm{range}\, I$ (Chapter 2, Section 2). So there is $R_1 > 0$ with $\bar B(\hat c, R_1) \cap \mathrm{range}\, I \subseteq T$. Take $R = \min(R_0, R_1)$ and $r = R/2$. $\square$

**Theorem (Values and support).** The values of $f$ lie in $[0, 1]$, and $f = 1$ on a neighbourhood of $c$. The support is
$$\mathrm{supp}\, f = \{x \in \mathrm{dom}\,\varphi \mid \hat\varphi(x) \in B(\hat c, R)\} = \{\hat\varphi^{-1}(y) \mid y \in B(\hat c, R) \cap \mathrm{range}\, I\}.$$
It is open and contains $c$.

*Proof.* The values are $0$ or values of $\beta$, which lie in $[0, 1]$. On $\mathrm{dom}\,\varphi$, $f = \beta \circ \hat\varphi$, and $\beta(y) \neq 0$ if and only if $y \in B(\hat c, R)$. Outside $\mathrm{dom}\,\varphi$, $f = 0$. This gives the first form. For the second, $B(\hat c, R) \cap \mathrm{range}\, I \subseteq T$ by the definition, and $\hat\varphi$ is a bijection from its source onto $T$, so a point $x$ of the source has $\hat\varphi(x) \in B(\hat c, R)$ if and only if $x$ is the image under $\hat\varphi^{-1}$ of a point of $B(\hat c, R) \cap \mathrm{range}\, I$. The first form is the preimage of an open set under a map continuous on an open set, so it is open. Finally, the set $\mathrm{dom}\,\varphi \cap \hat\varphi^{-1}(B(\hat c, r))$ is an open neighbourhood of $c$, and $f = 1$ on it, because $\beta = 1$ on $\bar B(\hat c, r)$. $\square$

**Theorem (Compact support).** Let $M$ be Hausdorff. Then $\overline{\mathrm{supp}}\, f$ is compact and contained in $\mathrm{dom}\,\varphi$.

*Proof.* Put $K = \{\hat\varphi^{-1}(y) \mid y \in \bar B(\hat c, R) \cap \mathrm{range}\, I\}$. The closed ball is compact, because $E$ is finite dimensional, and $\mathrm{range}\, I$ is closed, so their intersection is compact. It lies in $T$, where $\hat\varphi^{-1}$ is continuous, so $K$ is compact. In a Hausdorff space a compact set is closed (Volume 13, Chapter 5). The support lies in $K$ by the last theorem, so $\overline{\mathrm{supp}}\, f \subseteq K$. A closed subset of a compact set is compact, and $K$ lies in the image of $T$ under $\hat\varphi^{-1}$, which is $\mathrm{dom}\,\varphi$. $\square$

**Theorem (Smoothness).** Let $M$ be Hausdorff and of class $C^\infty$. Then $f$ is $C^\infty$.

*Proof.* A function that is $C^\infty$ at each point of its topological support is $C^\infty$ (Chapter 3), because outside the topological support it is $0$ on an open set. Let $x \in \overline{\mathrm{supp}}\, f$. By the last theorem, $x \in \mathrm{dom}\,\varphi$, an open set on which $f = \beta \circ \hat\varphi$. The extended chart $\hat\varphi$ is $C^\infty$ at $x$ as a map from $M$ to $E$, because $M$ is $C^\infty$, and $\beta$ is $C^\infty$. So $f$ is $C^\infty$ at $x$. $\square$

**Theorem (Neighbourhood basis).** Let $M$ be Hausdorff. For every neighbourhood $S$ of $c$ there is a smooth bump function $f$ at $c$ with $\overline{\mathrm{supp}}\, f \subseteq S$. The sets $\mathrm{supp}\, f$ for such $f$ form a basis of neighbourhoods of $c$.

*Proof.* The image of the filter of neighbourhoods of $\hat c$ within $\mathrm{range}\, I$ under $\hat\varphi^{-1}$ is the filter of neighbourhoods of $c$ (Chapter 2, Section 2). The sets $\bar B(\hat c, \rho) \cap \mathrm{range}\, I$ for small $\rho > 0$ form a basis of the first filter. So there is $\rho$ such that $\hat\varphi^{-1}(y) \in S$ for all $y \in \bar B(\hat c, \rho) \cap \mathrm{range}\, I$, and by the existence theorem $\rho$ can be taken small enough for a bump function $f$ with $R = \rho$. The proof of compact support gives $\overline{\mathrm{supp}}\, f \subseteq K \subseteq S$. The support of every bump function is a neighbourhood of $c$, so the supports form a basis. $\square$

**Theorem (Shrinking the outer radius).** Let $s \subseteq \mathrm{supp}\, f$ be closed in $M$. Then there is $\rho \in (0, R)$ with $s \subseteq \mathrm{dom}\,\varphi \cap \hat\varphi^{-1}(B(\hat c, \rho))$.

*Proof.* The image $\hat\varphi(s)$ is the set of points $y \in \bar B(\hat c, R) \cap \mathrm{range}\, I$ with $\hat\varphi^{-1}(y) \in s$, because $s$ lies in the support. It is closed, as the preimage of a closed set under a map that is continuous on a closed set. It lies in $B(\hat c, R)$ and in the compact ball $\bar B(\hat c, R)$, so it is compact. The continuous function $y \mapsto \|y - \hat c\|$ attains a maximum $m < R$ on it if it is not empty. Take $\rho \in (m, R)$, or any $\rho \in (0, R)$ if $s$ is empty. $\square$

After the shrinking, the bump function with radii $(\rho', R)$ for $\rho' \in (\rho, R)$ has the same support and is $1$ on $s$. This is the step that Section 2 uses to make bump functions equal to $1$ on prescribed closed sets.

### Examples

**Example (Normed spaces).** For $M = E$ with the model $\mathrm{id}_E$, the extended chart at $c$ is the identity and $T = E$. Every $0 < r < R$ is allowed, and $f$ is the bump function $\beta$ of Volume 17.

**Example (Half-line).** Let $M = [0, \infty)$ with the model of the half-line and $c = 0$. Then $\mathrm{range}\, I = [0, \infty)$, and $\bar B(0, R) \cap \mathrm{range}\, I = [0, R]$. The bump function is $1$ on $[0, r]$, positive on $[0, R)$ and $0$ on $[R, \infty)$. Its support $[0, R)$ is open in $M$.

**Example (The line with two origins).** Glue two copies of $\mathbb{R}$ along $\mathbb{R} \setminus \{0\}$ by the identity. The result $M$ has two origins $0_1, 0_2$, two charts, and smooth changes of charts, but it is not Hausdorff. Let $f$ be a bump function at $0_1$, defined with the chart of the first copy. Then $f(0_2) = 0$, since $0_2$ is not in the source of the chart. But $f(t) = \beta(t) \to 1$ as $t \to 0$ with $t \neq 0$, and these points also converge to $0_2$. So $f$ is not continuous at $0_2$, and $0_2$ lies in $\overline{\mathrm{supp}}\, f$ but not in the source of the chart. The Hausdorff condition in the theorems is needed.

### The library around it

::: mathlib
`SmoothBumpFunction.contMDiff` · `Mathlib.Geometry.Manifold.BumpFunction`

`SmoothBumpFunction.contMDiff` gives `ContMDiff I 𝓘(ℝ) ∞ f` under `T2Space M` and `IsManifold I ∞ M`. `SmoothBumpFunction.nhds_basis_tsupport c` says that the sets `tsupport f` form a basis of `𝓝 c`, and `SmoothBumpFunction.nhds_basis_support` gives the basis of supports among those `f` with `tsupport f ⊆ s`. The shrinking theorem is `SmoothBumpFunction.exists_r_pos_lt_subset_ball`, and `SmoothBumpFunction.updateRIn` replaces `rIn` with a new value in `(0, rOut)`.

<?decl SmoothBumpFunction.contMDiff?>
<?decl SmoothBumpFunction.nhds_basis_tsupport?>
<?decl SmoothBumpFunction.support_eq_inter_preimage?>
<?decl SmoothBumpFunction.tsupport_subset_chartAt_source?>
<?decl SmoothBumpFunction.exists_r_pos_lt_subset_ball?>
:::

The values and the neighbourhood of $1$ are `SmoothBumpFunction.mem_Icc` and `SmoothBumpFunction.eventuallyEq_one`. `SmoothBumpFunction.hasCompactSupport` is the compact support theorem. `SmoothBumpFunction.instNonempty` is the existence theorem without a bound on the radius. `SmoothBumpFunction.contMDiff_smul` says that `f • g` is smooth on $M$ when `g` is smooth on the source of the chart at `c`. The theorem `contMDiff_of_tsupport` of Chapter 3 is the reduction to the topological support used in the proof of smoothness. The bump functions of the model space are `ContDiffBump`, with the class `HasContDiffBump E` that holds for finite dimensional spaces.

Common errors of a learner:

- Applying `SmoothBumpFunction.contMDiff` on a manifold of class $C^n$ with $n$ finite. The theorem asks for `IsManifold I ∞ M`, because the extended chart of a $C^n$ manifold is only $C^n$.
- Forgetting `T2Space M` and looking for `SmoothBumpFunction.contMDiff` in a context without it. Without the Hausdorff condition the theorem is false.
- Reading `rOut` as a radius in $M$. It is a radius in the model space $E$, for the norm of $E$ and the extended chart at $c$.

### Exercises

1. (A) Show that $f(c) = 1$ and $c \in \mathrm{supp}\, f$.
2. (A) Let $f$ be a smooth bump function at $c$ and $g$ a $C^\infty$ function on $\mathrm{dom}\,\varphi$. Show that $x \mapsto f(x) g(x)$, extended by $0$, is $C^\infty$ on a Hausdorff $C^\infty$ manifold $M$.
3. (B) Let $M$ be a Hausdorff $C^\infty$ manifold, $K \subseteq M$ compact and $U \supseteq K$ open. Show that there is a $C^\infty$ function $g : M \to [0, \infty)$ with $g > 0$ on $K$ and $\overline{\mathrm{supp}}\, g \subseteq U$. Hint: cover $K$ by finitely many supports of bump functions.
4. (B) Improve Exercise 3 to $g = 1$ on $K$ and $g \le 1$. Hint: compose $g$ with a smooth function $\mathbb{R} \to [0, 1]$ that is $1$ on $[m, \infty)$, where $m = \min_K g$, and $0$ on $(-\infty, 0]$.
5. (B) Show that a Hausdorff $C^\infty$ manifold $M$ modelled on $\mathbb{R}^n$ with $n \ge 1$ has an infinite dimensional space of $C^\infty$ functions. Hint: take bump functions with disjoint supports at infinitely many points of one chart.
6. (C) On the line with two origins, describe all $C^\infty$ functions $M \to \mathbb{R}$. Show that every such function takes the same value at $0_1$ and $0_2$.

### Notes and history

Augustin-Louis Cauchy gave the function $e^{-1/x^2}$ as an example of a smooth function that is not the sum of its Taylor series at $0$. Bump functions are built from functions of this kind. The header of `Mathlib.Geometry.Manifold.BumpFunction` names Yury Kudryashov as author.

### Reference

<?reference?>
