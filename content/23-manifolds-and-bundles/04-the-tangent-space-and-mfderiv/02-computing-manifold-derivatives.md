---
title: Computing manifold derivatives
kind: theory
modules:
  - Mathlib.Geometry.Manifold.MFDeriv.FDeriv
  - Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
  - Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
  - Mathlib.Geometry.Manifold.MFDeriv.Atlas
explains:
  E3: [mfderiv_eq_fderiv, hasMFDerivAt_iff_hasFDerivAt, mfderiv_extChartAt_self]
  E2: [writtenInExtChartAt_model_space, mdifferentiableAt_iff_differentiableAt, HasFDerivAt.hasMFDerivAt, DifferentiableAt.mdifferentiableAt, mfderivWithin_eq_fderivWithin, uniqueMDiffOn_iff_uniqueDiffOn, mvfderiv, mvfderiv_eq_fderiv, mvfderiv_add, mvfderiv_mul, MDifferentiableAt.mvfderiv, Differentiable.comp_mdifferentiableAt, MDifferentiableAt.smul, mfderiv_id, mfderiv_const, mfderiv_fst, mfderiv_snd, mfderiv_prodMk, MDifferentiableAt.prodMk, mfderiv_prodMap, mfderiv_prod_eq_add, mfderiv_add, mfderiv_neg, mfderiv_sub, const_smul_mfderiv, MDifferentiableAt.add, HasMFDerivAt.mul, MDifferentiableAt.mul, ContinuousLinearMap.mfderiv_eq, mdifferentiableOn_extChartAt, hasMFDerivAt_extChartAt, isInvertible_mfderiv_extChartAt, mdifferentiable_chart, mdifferentiableOn_atlas, ModelWithCorners.hasMFDerivAt, OpenPartialHomeomorph.MDifferentiable.symm_comp_deriv, OpenPartialHomeomorph.MDifferentiable.mfderiv, mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt]
  E1: auto
families: []
requires: [V23.C02, V23.C03, V17.C01, V17.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Computing manifold derivatives

### Overview

Section 1 defined the derivative $Df(x)$ of a map between manifolds through the charts. This section computes it. For maps between normed spaces it is the Fréchet derivative. For maps into a normed space it is linear in the map and satisfies the rule of Leibniz. The identity, constants, projections and pairs have the expected derivatives. The derivative of a chart at its base point is the identity, and it is invertible on the whole source. A worked example identifies the tangent space of the sphere with the orthogonal complement of the point.

The notation is that of Section 1: $\varphi_x$ is the extended chart at $x$, $R$ is the range of the model $I$, and $f_x$ is $f$ written in the preferred charts at $x$ and at $f(x)$.

### Definitions

A normed space $F$ is a manifold with the trivial model $\mathcal{I}(\Bbbk, F)$, whose only chart is the identity. Its tangent space at each point is $F$.

**Definition (Differential of a vector valued map).** Let $f : M \to F$ be a map into a normed space. Its differential at $x$ is $Df(x)$ seen as a linear map $T_xM \to F$, with values in $F$ itself instead of the tangent space $T_{f(x)}F$.

The two spaces are equal by definition, so the differential and $Df(x)$ are the same map. The difference is in the types. In Mathlib the differential is `mvfderiv I f x`, with notation `d% f x`. It is the derivative of $f$ composed with `NormedSpace.fromTangentSpace`, the identification of $T_{f(x)}F$ with $F$. For $F = \Bbbk$ it is the exterior derivative of the function $f$.

**Definition (Product charts).** The preferred chart of $M \times M'$ at $(x, y)$ is the product of the preferred charts, with model $I \times I'$. Its extended chart is $\varphi_x \times \varphi'_y$, and the range of $I \times I'$ is $R \times R'$. This is Chapter 2.

### Theorems and proofs

**Theorem (Maps between normed spaces).** Let $f : E \to E'$ and $L : E \to E'$ continuous linear. Then $f$ has derivative $L$ at $x$ in the sense of manifolds if and only if $f$ has Fréchet derivative $L$ at $x$. In particular $Df(x)$ is the Fréchet derivative of $f$ at $x$, also when $f$ is not differentiable, since both are then $0$.

*Proof.* All extended charts of $E$ and $E'$ are the identity, so $f_x = f$, and $R = E$. A derivative within $E$ is a derivative. A map with a Fréchet derivative at $x$ is continuous at $x$. So the two conditions agree. The definitions of `mfderiv` and `fderiv` both give $0$ where $f$ is not differentiable, and otherwise give the unique derivative. $\square$

**Theorem (Maps into a normed space).** Let $f, g : M \to F$ be differentiable at $x$ and $c \in \Bbbk$. Then $f + g$ and $cf$ are differentiable at $x$, and
$$D(f + g)(x) = Df(x) + Dg(x), \qquad D(cf)(x) = c\,Df(x).$$

*Proof.* The chart of $F$ is the identity, so $f_x = f \circ \varphi_x^{-1}$, and $(f + g)_x = f_x + g_x$. Continuity of $f + g$ at $x$ is clear. By Volume 17 the sum of maps differentiable within $R$ at $a = \varphi_x(x)$ is differentiable within $R$, with derivative the sum of the derivatives. Since $R$ has unique differentials at $a$, the derivative within $R$ of $f_x + g_x$ is $D f(x) + D g(x)$. The case $cf$ is the same. $\square$

**Theorem (Rule of Leibniz).** Let $A$ be a normed commutative ring that is a normed algebra over $\Bbbk$. Let $p, q : M \to A$ have derivatives $p'$ and $q'$ at $x$. Then $pq$ has derivative $p(x)\,q' + q(x)\,p'$ at $x$.

*Proof.* As above $(pq)_x = p_x q_x$ with $p_x = p \circ \varphi_x^{-1}$. Here $p_x(a) = p(x)$, because $\varphi_x^{-1}(a) = x$. The product rule of Volume 17 within the set $R$ gives the derivative $p_x(a)\,q' + q_x(a)\,p' = p(x)\,q' + q(x)\,p'$. Continuity of $pq$ at $x$ follows from the continuity of $p$ and $q$. $\square$

**Theorem (Elementary maps).** Let $x \in M$, $y \in M'$ and $c \in M'$.

1. The identity of $M$ has derivative $\mathrm{id}$ at $x$.
2. The constant map with value $c$ has derivative $0$ at $x$.
3. The projections $M \times M' \to M$ and $M \times M' \to M'$ have derivatives the linear projections $E \times E' \to E$ and $E \times E' \to E'$ at $(x, y)$.
4. If $f : M \to M'$ and $g : M \to M''$ are differentiable at $x$, then $D(f, g)(x) = (Df(x), Dg(x))$.

*Proof.* 1. The written map is $\varphi_x \circ \varphi_x^{-1}$. It is the identity on the target of $\varphi_x$, which is a neighbourhood of $a$ within $R$. So its derivative within $R$ at $a$ is the identity.

2. The written map is constant with value $\varphi'_c(c)$, with derivative $0$.

3. Put $\Phi = \varphi_x \times \varphi'_y$. The written first projection is $(u, w) \mapsto \varphi_x(\varphi_x^{-1}(u))$. On the target of $\Phi$, a neighbourhood of $\Phi(x, y)$ within $R \times R'$, it equals $(u, w) \mapsto u$. That map is continuous linear, and it is its own derivative. The second projection is the same.

4. The chart of $M' \times M''$ at $(f(x), g(x))$ is the product of the charts, so the written pair is $(f_x, g_x)$. A pair of maps differentiable within $R$ at $a$ is differentiable, with derivative the pair of derivatives (Volume 17). The pair $(f, g)$ is continuous at $x$. $\square$

**Theorem (Derivative of a chart).** Let $M$ be a manifold of class $C^1$ and $x \in M$. View $\varphi_x$ as a map from $M$ to the normed space $E$. Then $\varphi_x$ is differentiable at each point $y$ of its source, $D\varphi_x(x) = \mathrm{id}_E$, and $D\varphi_x(y)$ is invertible for each $y$ in the source.

*Proof.* Let $y$ be in the source of $\varphi_x$, and write $b = \varphi_y(y)$. The chart of $E$ is the identity, so the written map at $y$ is the change of charts $\tau = \varphi_x \circ \varphi_y^{-1}$. Since $M$ is of class $C^1$, $\tau$ is $C^1$ within $R$ near $b$, so it is differentiable within $R$ at $b$. The map $\varphi_x$ is continuous on its source, which is open. So $\varphi_x$ is differentiable at $y$, with derivative $T = D\tau(b)$ within $R$.

For $y = x$, the map $\tau$ is $\varphi_x \circ \varphi_x^{-1}$, which is the identity near $b$ within $R$. So $D\varphi_x(x) = \mathrm{id}_E$.

For invertibility, let $\sigma = \varphi_y \circ \varphi_x^{-1}$, the inverse change of charts, and $S = D\sigma(\tau(b))$ within $R$. Both $\tau$ and $\sigma$ map $R$ into $R$. Near $b$ within $R$, $\sigma \circ \tau$ is the identity, and near $\tau(b)$ within $R$, $\tau \circ \sigma$ is the identity. The chain rule within sets and the uniqueness of derivatives within $R$ give $S \circ T = \mathrm{id}_E$ and $T \circ S = \mathrm{id}_E$. So $T$ is invertible. $\square$

The derivative at $y$ of the chart at $x$ is the derivative of a change of charts. Chapter 5 calls these maps the coordinate changes of the tangent bundle.

### Examples

**Example (The tangent space of the sphere).** Let $E$ be a real inner product space of dimension $n + 1$, let $S$ be its unit sphere with the manifold structure of Chapter 2, and let $\iota : S \to E$ be the inclusion. For $v \in S$, the derivative $D\iota(v) : T_vS \to E$ is injective, and its range is $v^\perp$.

*Proof.* The map $\iota$ is smooth by Chapter 2, so it is differentiable. Let $N(z) = \langle z, z \rangle$ on $E$. Its Fréchet derivative is $DN(v)h = 2\langle v, h \rangle$. The map $N \circ \iota$ is constant with value $1$, so the chain rule and the elementary maps give $DN(v) \circ D\iota(v) = 0$. So every vector in the range of $D\iota(v)$ is orthogonal to $v$.

Mathlib takes the chart at $v$ to be the stereographic projection from $-v$, followed by a linear isometry onto $\mathbb{R}^n$. The projection is the restriction to $S$ of a map $\sigma : E \to \mathbb{R}^n$ that is smooth on the open set $\{z : \langle -v, z \rangle \ne 1\}$, which contains $v$. So $\varphi_v = \sigma \circ \iota$ near $v$, and the chain rule gives
$$\mathrm{id} = D\varphi_v(v) = D\sigma(v) \circ D\iota(v).$$
So $D\iota(v)$ is injective. Its range has dimension $n = \dim T_vS$. It lies in $v^\perp$, which also has dimension $n$, so the range is $v^\perp$. $\square$

**Example (The height function on the circle).** Let $S \subseteq \mathbb{R}^2$ be the unit circle and $h(z) = z_2$. Then $h = \pi_2 \circ \iota$ with the linear map $\pi_2(z) = z_2$, so $Dh(v) = \pi_2 \circ D\iota(v)$. By the previous example the range of $D\iota(v)$ is $v^\perp$, spanned by $(-v_2, v_1)$, and $\pi_2(-v_2, v_1) = v_1$. So $Dh(v) = 0$ if and only if $v_1 = 0$, that is $v = (0, 1)$ or $v = (0, -1)$. These are the maximum and the minimum of $h$.

**Example (A product).** Let $f : \mathbb{R} \to \mathbb{R}$ and $g : \mathbb{R} \to \mathbb{R}^2$ be $f(t) = t^3$ and $g(t) = (t, e^t)$. The map $\mathbb{R} \to \mathbb{R} \times \mathbb{R}^2$, $t \mapsto (f(t), g(t))$, has derivative $s \mapsto (3t^2 s, (s, e^t s))$ at $t$, by part 4 of the theorem on elementary maps and the first theorem.

### The library around it

The file `Mathlib.Geometry.Manifold.MFDeriv.FDeriv` compares the manifold notions with the Fréchet notions for maps between normed spaces. `Mathlib.Geometry.Manifold.MFDeriv.NormedSpace` treats maps into a normed space and defines `mvfderiv`. `Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions` computes the elementary derivatives, and `Mathlib.Geometry.Manifold.MFDeriv.Atlas` treats the charts.

::: mathlib
`mfderiv_eq_fderiv` · `Mathlib.Geometry.Manifold.MFDeriv.NormedSpace`

For $f : E \to E'$, `mfderiv_eq_fderiv` states that `mfderiv% f x` is `fderiv 𝕜 f x` between two copies of `NormedSpace.fromTangentSpace`. These maps are identities, and they only change the types. `hasMFDerivAt_iff_hasFDerivAt` has no casts. The simp lemma `writtenInExtChartAt_model_space` says that $f_x = f$. To differentiate a composition of a manifold map with a map of normed spaces, use `Differentiable.comp_mdifferentiableAt`.

<?decl mfderiv_eq_fderiv?>
<?decl hasMFDerivAt_iff_hasFDerivAt?>
<?decl mvfderiv?>
<?decl mvfderiv_mul?>
:::

::: mathlib
`mfderiv_prodMk` · `Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions`

The elementary derivatives are `mfderiv_id`, `mfderiv_const`, `mfderiv_fst`, `mfderiv_snd` and `mfderiv_prodMk`, whose value is `ContinuousLinearMap.prod`. `mfderiv_prod_eq_add` writes the derivative of a map on $M \times M'$ as the sum of its partial derivatives. `ContinuousLinearMap.mfderiv_eq` says that a continuous linear map is its own derivative. The rule of Leibniz is `HasMFDerivAt.mul` for commutative rings, and `mvfderiv_mul` in the form $d(fg) = f\,dg + g\,df$.

<?decl mfderiv_prodMk?>
<?decl mfderiv_prod_eq_add?>
<?decl HasMFDerivAt.mul?>
:::

::: mathlib
`mfderiv_extChartAt_self` · `Mathlib.Geometry.Manifold.MFDeriv.Atlas`

The theorem on charts is `mdifferentiableOn_extChartAt`, `mfderiv_extChartAt_self` and `isInvertible_mfderiv_extChartAt`, all under `IsManifold I 1 M`. `hasMFDerivAt_extChartAt` gives the derivative at $y$ as the derivative of the chart `chartAt H x`, with values in $H$ modelled by $I$. `mdifferentiable_chart` packs the chart and its inverse into `OpenPartialHomeomorph.MDifferentiable`, and `OpenPartialHomeomorph.MDifferentiable.mfderiv` turns its derivative into a continuous linear equivalence. The identification with the coordinate changes of the tangent bundle, `mfderiv_chartAt_eq_tangentCoordChange`, belongs to Chapter 5.

<?decl mfderiv_extChartAt_self?>
<?decl isInvertible_mfderiv_extChartAt?>
<?decl mdifferentiable_chart?>
<?decl tangentCoordChange?>
:::

The tangent space and the inclusion of the sphere are in the files of Chapter 2: `range_mvfderiv_subtypeVal` is the first example, and `injective_mvfderiv_subtypeVal_sphere` its injectivity part.

Common errors of a learner:

- Reading `mfderiv_eq_fderiv` as a rewrite that removes all casts. The goal keeps `NormedSpace.fromTangentSpace`, and `hasMFDerivAt_iff_hasFDerivAt` is often easier.
- Using `mfderiv_add` for maps into a manifold. It needs values in a normed space, where addition exists.
- Forgetting `IsManifold I 1 M` for the lemmas on charts. Without it the changes of charts need not be differentiable.

### Exercises

1. (A) Let $f : M \to \Bbbk$ be differentiable at $x$ with $f(x) \ne 0$. Show that $1/f$ is differentiable at $x$ and $D(1/f)(x) = -f(x)^{-2}\,Df(x)$. Hint: compose with $t \mapsto 1/t$ and use the first theorem.
2. (A) Compute the derivative of $(x, y) \mapsto (y, x)$ on $M \times M'$. Hint: use the projections and pairs.
3. (B) Let $A : E \to E'$ be continuous linear and $f : M \to E$ be differentiable at $x$. Show that $D(A \circ f)(x) = A \circ Df(x)$.
4. (B) Let $S \subseteq \mathbb{R}^3$ be the unit sphere and $h(z) = z_3$. Find the points where $Dh(v) = 0$.
5. (B) Let $f : M \to \Bbbk$ be differentiable at $x$ and $n \ge 1$. Show that $D(f^n)(x) = n f(x)^{n-1} Df(x)$. Hint: induction with the rule of Leibniz.
6. (B) Let $M$ be of class $C^1$ and $y$ in the sources of the charts at $x$ and $x'$. Prove that $D(\varphi_{x'} \circ \varphi_x^{-1})(\varphi_x(y))$ within $R$ equals $D\varphi_{x'}(y) \circ D\varphi_x(y)^{-1}$.
7. (C) Let $E$ be a real inner product space of dimension $n + 1$ and $f : E \to \mathbb{R}$ differentiable. Show that $v \in S$ is a critical point of $f \circ \iota$ if and only if $\nabla f(v)$ is a multiple of $v$. Hint: this is the method of Lagrange multipliers.

### Notes and history

The computation of the tangent space of the sphere as $v^\perp$ is the classical description of the tangent space of a submanifold of a Euclidean space as the kernel of the derivative of a defining function. The file headers of the four files of this section name Sébastien Gouëzel and Floris van Doorn as authors.

### Reference

<?reference?>
