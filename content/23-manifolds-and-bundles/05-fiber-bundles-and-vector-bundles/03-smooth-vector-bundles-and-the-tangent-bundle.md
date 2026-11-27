---
title: Smooth vector bundles and the tangent bundle
kind: theory
modules:
  - Mathlib.Geometry.Manifold.VectorBundle.Basic
  - Mathlib.Geometry.Manifold.VectorBundle.FiberwiseLinear
  - Mathlib.Geometry.Manifold.VectorBundle.Tangent
  - Mathlib.Geometry.Manifold.VectorBundle.Hom
  - Mathlib.Geometry.Manifold.VectorBundle.Pullback
  - Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
  - Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
  - Mathlib.Geometry.Manifold.VectorBundle.Riemannian
  - Mathlib.Geometry.Manifold.ContMDiffMFDeriv
  - Mathlib.Geometry.Manifold.MFDeriv.Tangent
  - Mathlib.Geometry.Manifold.Riemannian.Basic
  - Mathlib.Geometry.Manifold.Riemannian.PathELength
explains:
  E3: [ContMDiffVectorBundle, Bundle.TotalSpace.isManifold, tangentBundleCore, ContMDiff.contMDiff_tangentMap]
  E2: [ContMDiffVectorBundle.contMDiffOn_coordChangeL, VectorBundleCore.IsContMDiff, VectorBundleCore.instContMDiffVectorBundle, contMDiffFiberwiseLinear, mem_contMDiffFiberwiseLinear_iff, FiberwiseLinear.openPartialHomeomorph, ContMDiffFiberwiseLinear.hasGroupoid, FiberBundle.chartedSpace, Bundle.contMDiff_proj, Bundle.contMDiffAt_totalSpace_iff, Bundle.contMDiffAt_section_iff, Bundle.contMDiff_zeroSection, Bundle.Trivial.contMDiffVectorBundle, Bundle.Prod.contMDiffVectorBundle, ContMDiffVectorBundle.pullback, ContMDiffVectorBundle.continuousLinearMap, contMDiffAt_hom_bundle, ContMDiffVectorBundle.continuousAlternatingMap, mdifferentiableAt_totalSpace, mdifferentiableAt_section, tangentBundleCore_coordChange, tangentBundleCore_baseSet, tangentCoordChange_def, tangentCoordChange_self, tangentCoordChange_comp, continuousOn_tangentCoordChange, hasFDerivWithinAt_tangentCoordChange, contDiffOn_fderiv_coord_change, tangentBundleCore.isContMDiff, TangentSpace.fiberBundle, TangentSpace.vectorBundle, TangentBundle.contMDiffVectorBundle, TangentBundle.chartAt, TangentBundle.trivializationAt_apply, tangentBundleModelSpaceHomeomorph, tangentBundleModelSpaceDiffeomorph, inTangentCoordinates, inTangentCoordinates_eq_mfderiv_comp, ContMDiffAt.mfderiv, ContMDiff.continuous_tangentMap, tangentMap_chart, mfderiv_chartAt_eq_tangentCoordChange, equivTangentBundleProd, contMDiff_equivTangentBundleProd, IsContMDiffRiemannianBundle, Bundle.ContMDiffRiemannianMetric, ContMDiff.inner_bundle, Manifold.pathELength, Manifold.pathELength_eq_lintegral_mfderiv_Icc, Manifold.riemannianEDist, Manifold.riemannianEDist_triangle, Manifold.riemannianEDist_le_pathELength, IsRiemannianManifold, PseudoEMetricSpace.ofRiemannianMetric, EMetricSpace.ofRiemannianMetric, lintegral_fderiv_lineMap_eq_edist]
  E1: auto
families: []
requires: [V23.C02, V23.C03, V23.C04, V17.C02, V17.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Smooth vector bundles and the tangent bundle

### Overview

A vector bundle over a manifold is smooth when its coordinate changes are smooth functions of the base point. Its total space is then a manifold, and the projection and the zero section are smooth maps. The tangent bundle is the main example. Its coordinate changes are the derivatives of the changes of charts.

This section uses the vector bundles of Section 2. It proves that the total space of a smooth vector bundle is a manifold, gives a criterion for the smoothness of maps into it, builds the tangent bundle, and proves that the tangent map of a $C^n$ map is of class $C^{m}$ for $m + 1 \le n$. It closes with Riemannian metrics and the Riemannian distance.

### Definitions

Let $\Bbbk$ be a nontrivially normed field, $n \in \mathbb{N} \cup \{\infty, \omega\}$, and $B$ a manifold with model with corners $I_B$ on $E_B$. Let $E$ be a vector bundle over $B$ with fiber $F$, as in Section 2.

**Definition (Smooth vector bundle).** The bundle $E$ is a $C^n$ vector bundle if for any two trivializations $e, e'$ of its atlas, the map $b \mapsto g_{e e'}(b) \in L(F, F)$ is $C^n$ on $U \cap U'$, as a map from the manifold $B$ to the normed space $L(F, F)$.

**Definition (Fiberwise linear groupoid).** A partial homeomorphism of $B \times F$ is fiberwise linear of class $C^n$ if its source is $U \times F$ for an open $U$ and it has the form $(b, v) \mapsto (b, \varphi(b) v)$, where $\varphi : U \to L(F, F)$ takes invertible values and $b \mapsto \varphi(b)$ and $b \mapsto \varphi(b)^{-1}$ are $C^n$ on $U$. These maps form a structure groupoid on $B \times F$.

**Definition (Charts of the total space).** Let $p \in \mathrm{Tot}(E)$ with $\pi(p) = b$, let $e$ be the trivialization of the atlas at $b$ and $\phi$ the chart of $B$ at $b$. The chart of $\mathrm{Tot}(E)$ at $p$ is $(\phi \times \mathrm{id}_F) \circ e$, with values in $H_B \times F$. The model with corners is $I_B \times \mathrm{id}_F$.

**Definition (Tangent bundle).** Let $M$ be a $C^1$ manifold modelled on $I : H \to E$. The tangent bundle core has index set the atlas of $M$, base sets the chart sources, $i(x)$ the preferred chart at $x$, and
$$g_{\phi \psi}(x) = \mathrm{fderivWithin}\bigl(\tilde\psi \circ \tilde\phi^{-1}\bigr)(\mathrm{range}\, I)\bigl(\tilde\phi(x)\bigr),$$
where $\tilde\phi = I \circ \phi$ is the extended chart. The tangent bundle $TM$ is the bundle that this core defines. Its fiber at $x$ is $T_x M = E$, and a vector is written in the preferred chart at $x$.

**Definition (Tangent map).** For $f : M \to N$, the tangent map is $Tf : TM \to TN$, $(x, v) \mapsto (f(x), Df_x(v))$, where $Df_x$ is `mfderiv` of Chapter 4.

**Definition (Riemannian manifold).** Let $\Bbbk = \mathbb{R}$. A Riemannian metric of class $C^n$ on $M$ is a family of inner products on the tangent spaces that is a $C^n$ section of the bundle of bilinear forms. The length of a $C^1$ path $\gamma : [a, b] \to M$ is $\int_a^b \|\gamma'(t)\| \, dt$, and the Riemannian distance of $x, y$ is the infimum of the lengths of $C^1$ paths from $x$ to $y$. An extended metric space with a Riemannian metric is a Riemannian manifold if its distance is the Riemannian distance.

::: mathlib
`ContMDiffVectorBundle` · `Mathlib.Geometry.Manifold.VectorBundle.Basic`

`ContMDiffVectorBundle n F E IB` is a `Prop` class on top of `VectorBundle 𝕜 F E`. Its field asks `ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n` of each coordinate change on the intersection of the base sets. The instance `Bundle.TotalSpace.isManifold` makes the total space a `C^n` manifold modelled on `IB.prod 𝓘(𝕜, F)`. The definition `tangentBundleCore I M` is the core of the tangent bundle, a `VectorBundleCore 𝕜 M E (atlas H M)`.

<?decl ContMDiffVectorBundle?>
<?decl Bundle.TotalSpace.isManifold?>
<?decl tangentBundleCore?>
<?decl tangentBundleCore_coordChange?>
:::

### Theorems and proofs

**Theorem (The total space is a manifold).** Let $B$ be a $C^n$ manifold and $E$ a $C^n$ vector bundle over $B$. Then $\mathrm{Tot}(E)$ with the charts above is a $C^n$ manifold modelled on $I_B \times \mathrm{id}_F$.

*Proof.* Let $p, p'$ be points over $b, b'$, with trivializations $e, e'$ and charts $\phi, \phi'$ of $B$. The change of charts from $p'$ to $p$ is
$$(y, w) \mapsto \bigl(\phi(\phi'^{-1}(y)),\ g_{e' e}(\phi'^{-1}(y))\, w\bigr)$$
on its domain. The first component is a change of charts of $B$, which is $C^n$ in the extended charts. In the second component, $y \mapsto g_{e' e}(\phi'^{-1}(y))$ is $C^n$ within the range of $I_B$, because $g_{e' e}$ is $C^n$ on $U \cap U'$. Evaluation $L(F, F) \times F \to F$ is continuous and bilinear, so it is $C^\infty$, and the composite $(y, w) \mapsto g_{e' e}(\phi'^{-1}(y)) w$ is $C^n$. The range of $I_B \times \mathrm{id}_F$ is $\mathrm{range}\, I_B \times F$, so the change of charts is $C^n$ within it. $\square$

Mathlib first shows that the changes of trivializations lie in the fiberwise linear groupoid (`ContMDiffFiberwiseLinear.hasGroupoid`).

**Theorem (Maps into the total space).** Let $N$ be a manifold, $f : N \to \mathrm{Tot}(E)$ and $x_0 \in N$, and let $e$ be the trivialization at $\pi(f(x_0))$. Then $f$ is $C^n$ at $x_0$ if and only if $\pi \circ f$ is $C^n$ at $x_0$ and $x \mapsto \mathrm{pr}_2(e(f(x)))$ is $C^n$ at $x_0$ as a map into $F$.

*Proof.* Write $b_0 = \pi(f(x_0))$ and $\phi$ for the chart of $B$ at $b_0$. In both directions $f$ is continuous at $x_0$. If $f$ is $C^n$ at $x_0$, this is part of the definition. Under the two conditions, $\pi \circ f$ is continuous at $x_0$, so near $x_0$ the point $\pi(f(x))$ lies in $U$, and $f(x) = e^{-1}(\pi(f(x)), \mathrm{pr}_2(e(f(x))))$ is continuous at $x_0$. So near $x_0$ the point $f(x)$ lies in the source of the chart at $f(x_0)$, and in this chart $f$ is written
$$x \mapsto \bigl(\phi(\pi(f(x))),\ \mathrm{pr}_2(e(f(x)))\bigr).$$
A map into a product is $C^n$ if and only if both components are. The first component is $\pi \circ f$ written in the chart $\phi$, which is $C^n$ at $x_0$ if and only if $\pi \circ f$ is. $\square$

**Corollary (Projection and zero section).** The projection $\pi$ is $C^n$, and the zero section $b \mapsto (b, 0)$ is $C^n$.

*Proof.* In the chart at $p$ and the chart $\phi$ at $\pi(p)$, the projection is written $(y, w) \mapsto y$, which is $C^\infty$. For the zero section $s$, $\pi \circ s = \mathrm{id}_B$ and $\mathrm{pr}_2(e(b, 0)) = 0$ for $b \in U$, since $e$ is linear on fibers. Both are $C^n$. $\square$

**Theorem (The tangent bundle).** Let $M$ be a $C^{n+1}$ manifold. The maps $g_{\phi\psi}$ form a vector bundle core, and the tangent bundle is a $C^n$ vector bundle. So $TM$ is a $C^n$ manifold.

*Proof.* Write $s = \mathrm{range}\, I$, which has unique differentials and is mapped into itself by each $\tilde\psi \circ \tilde\phi^{-1}$. For $x$ in the source of $\phi$, the map $\tilde\phi \circ \tilde\phi^{-1}$ is the identity on $s$ near $\tilde\phi(x)$, so $g_{\phi\phi}(x) = \mathrm{id}$. For three charts and $x$ in their sources, $\tilde\chi \circ \tilde\phi^{-1} = (\tilde\chi \circ \tilde\psi^{-1}) \circ (\tilde\psi \circ \tilde\phi^{-1})$ on $s$ near $\tilde\phi(x)$. Both factors are differentiable within $s$, so the chain rule within sets of Volume 17, Chapter 2 gives $g_{\psi\chi}(x) \circ g_{\phi\psi}(x) = g_{\phi\chi}(x)$. The change of charts $\tilde\psi \circ \tilde\phi^{-1}$ is $C^{n+1}$ within $s$ on its domain. By Volume 17, Chapter 4, its derivative within $s$ is $C^n$ there. Composed with the extended chart $\tilde\phi$, this says that $x \mapsto g_{\phi\psi}(x)$ is $C^n$ on the intersection of the sources, as a map from $M$. For $n = 0$ this is the continuity that a vector bundle core needs. Section 2 gives the vector bundle, and the first theorem gives the manifold. $\square$

**Theorem (Tangent maps).** Let $M, N$ be $C^1$ manifolds and $f : M \to N$ a $C^n$ map, and let $m + 1 \le n$. Then $Tf : TM \to TN$ is $C^m$. If $n \ge 1$, then $Tf$ is continuous.

*Proof.* Fix $p = (x_0, v_0)$ and write $\phi, \psi$ for the charts at $x_0$ and $f(x_0)$, and $\hat f = \tilde\psi \circ f \circ \tilde\phi^{-1}$. A vector at $x$ is written in the chart at $x$. The trivialization at $x_0$ maps it to chart $\phi$ by $g_{\phi_x \phi}(x)$, the derivative of a change of charts. By the chain rule of Chapter 4,
$$g_{\psi_{f(x)} \psi}(f(x)) \circ Df_x \circ g_{\phi \phi_x}(x) = D_s \hat f\bigl(\tilde\phi(x)\bigr).$$
So $Tf$ written in the charts at $p$ and $Tf(p)$ is
$$(y, w) \mapsto \bigl(\hat f(y),\ D_s \hat f(y)\, w\bigr)$$
near $\tilde\phi(x_0)$. The map $\hat f$ is $C^n$ within $s$ near $\tilde\phi(x_0)$, because $f$ is continuous and $C^n$. Its derivative within $s$ is $C^{n-1}$, hence $C^m$. Evaluation is bilinear and continuous, so the second component is $C^m$. For continuity, take $m = 0$. $\square$

### Examples

**Example (Normed spaces).** For $M = E$ with the model $\mathrm{id}_E$, all coordinate changes are $\mathrm{id}$, so $TE$ is homeomorphic to $E \times E$. For $f : E \to E'$ the tangent map is $(x, v) \mapsto (f(x), Df(x) v)$.

**Example (Riemannian distance of an inner product space).** Let $F$ be a real inner product space with the constant metric. For a $C^1$ path $\gamma$ from $x$ to $y$ on $[0, 1]$,
$$\|y - x\| = \Bigl\|\int_0^1 \gamma'(t)\, dt\Bigr\| \le \int_0^1 \|\gamma'(t)\|\, dt,$$
and the segment $t \mapsto x + t(y - x)$ has length $\|y - x\|$. So the Riemannian distance is $\|y - x\|$, and $F$ is a Riemannian manifold.

**Example (Trivial and product bundles).** The trivial bundle $B \times F$ has constant coordinate changes, so it is $C^n$ for all $n$. For $C^n$ bundles $E_1, E_2$, the Whitney sum has coordinate changes $b \mapsto g_1(b) \times g_2(b)$, a composite of $(g_1, g_2)$ with a continuous linear map, so it is $C^n$.

**Example (Pullback).** For a $C^n$ map $f : B' \to B$, the coordinate changes $g_{e e'} \circ f$ of $f^* E$ are $C^n$ by the chain rule for $C^n$ maps of Chapter 3.

**Example (Tangent bundle of the circle).** Take the stereographic projections of $S^1$ from the north and the south pole as charts. The change of charts is $t \mapsto 1/t$ on $\mathbb{R} \setminus \{0\}$. The coordinate change of $TS^1$ at $t$ is multiplication by the derivative $-1/t^2$.

### The library around it

::: mathlib
`ContMDiff.contMDiff_tangentMap` · `Mathlib.Geometry.Manifold.ContMDiffMFDeriv`

`ContMDiff.contMDiff_tangentMap` takes `ContMDiff I I' n f` and `m + 1 ≤ n` and gives `ContMDiff I.tangent I'.tangent m (tangentMap I I' f)`, under `IsManifold I 1 M` and `IsManifold I' 1 M'`. It is the case of the whole space of `ContMDiffOn.contMDiffOn_tangentMapWithin`. `ContMDiffAt.mfderiv` is a more general statement on the derivatives of families of maps, written with `inTangentCoordinates`.

<?decl ContMDiff.contMDiff_tangentMap?>
<?decl ContMDiff.continuous_tangentMap?>
<?decl Bundle.contMDiffAt_totalSpace_iff?>
<?decl TangentBundle.contMDiffVectorBundle?>
:::

`TangentSpace.fiberBundle` and `TangentSpace.vectorBundle` are the instances from the core, and `TangentBundle.contMDiffVectorBundle` needs `IsManifold I (n + 1) M`. `TangentBundle.trivializationAt_apply` gives the trivialization at $x$ as the derivative of a change of extended charts. `mfderiv_chartAt_eq_tangentCoordChange` identifies the coordinate change with the derivative of a chart. `tangentBundleModelSpaceHomeomorph I` is the homeomorphism of `TangentBundle I H` with `ModelProd H E`. `Bundle.contMDiffAt_section_iff` is the criterion for sections, and `Bundle.contMDiff_zeroSection` is the zero section. The instances `ContMDiffVectorBundle.pullback`, `ContMDiffVectorBundle.continuousLinearMap` and `ContMDiffVectorBundle.continuousAlternatingMap` cover pullbacks, Hom bundles and bundles of alternating maps.

::: mathlib
`IsRiemannianManifold` · `Mathlib.Geometry.Manifold.Riemannian.Basic`

`IsRiemannianManifold I M` asks that `edist x y = riemannianEDist I x y`. `Manifold.riemannianEDist I x y` is the infimum, over paths from `x` to `y` that are $C^1$, of the integral of the norm of the derivative. `Manifold.pathELength I γ a b` is the length of `γ` on `Icc a b`, with values in `ℝ≥0∞`. `EMetricSpace.ofRiemannianMetric` builds the distance from a continuous Riemannian metric on a $C^1$ manifold, with the same topology. `IsContMDiffRiemannianBundle IB n F E` says that the metric of a bundle is $C^n$.

<?decl IsRiemannianManifold?>
<?decl Manifold.riemannianEDist?>
<?decl Manifold.pathELength?>
<?decl IsContMDiffRiemannianBundle?>
:::

Common errors of a learner:

- Expecting $TM$ to be a $C^1$ manifold when $M$ is only $C^1$. The theorem needs $M$ of class $C^{n+1}$ for $TM$ of class $C^n$, and Mathlib finds the instance for $C^1$ from `IsManifold I 2 M`.
- Writing the model of $TM$ as `I.prod I`. It is `I.tangent`, which is `I.prod 𝓘(𝕜, E)`.
- Forgetting that a vector of $T_x M$ is written in the chart at $x$, not in a fixed chart.

### Exercises

1. (A) Show from the definition that the coordinate change of $TM$ from a chart to itself is the identity at each point of its source.
2. (A) Show that for a $C^1$ map $f : M \to N$ and $g : N \to P$, $T(g \circ f) = Tg \circ Tf$.
3. (B) Let $E$ be a $C^n$ vector bundle and $s, t$ $C^n$ sections. Show that $s + t$ is a $C^n$ section.
4. (B) Show that a $C^n$ map $f : B \to F$ gives a $C^n$ section $b \mapsto (b, f(b))$ of the trivial bundle, and that every $C^n$ section of $B \times F$ has this form.
5. (B) Let $M$ be a $C^2$ manifold. Show that the projection $TM \to M$ is a submersion in the sense of Chapter 7: its derivative is surjective at each point.
6. (C) Let $M$ be a Riemannian manifold and $\gamma : [0, 1] \to M$ a $C^1$ path. Show that the length of $\gamma \circ \alpha$ equals the length of $\gamma$ for each $C^1$ increasing bijection $\alpha : [0, 1] \to [0, 1]$.

### Notes and history

Riemannian metrics come from the habilitation lecture of Bernhard Riemann in 1854. The header of `Mathlib.Geometry.Manifold.VectorBundle.Basic` and that of `Mathlib.Geometry.Manifold.VectorBundle.Tangent` name Floris van Doorn and Heather Macbeth as authors. The header of `Mathlib.Geometry.Manifold.ContMDiffMFDeriv` names Sébastien Gouëzel and Floris van Doorn, and the headers of the two Riemannian files name Sébastien Gouëzel.

### Reference

<?reference?>
