---
title: Extended charts
kind: theory
modules:
  - Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
explains:
  E3: [extChartAt, ModelWithCorners.extendCoordChange, writtenInExtChartAt]
  E2: [OpenPartialHomeomorph.extend, extChartAt_source, extChartAt_target, extChartAt_coe, extChartAt_coe_symm, isOpen_extChartAt_source, isOpen_extChartAt_target, map_extChartAt_nhds, map_extChartAt_symm_nhdsWithin_range, extChartAt_target_mem_nhdsWithin, extChartAt_target_mem_nhds, extChartAt_target_subset_range, uniqueDiffOn_extChartAt_target, extChartAt_preimage_mem_nhds, extChartAt_model_space_eq_id, extChartAt_prod, ModelWithCorners.extendCoordChange_source, ModelWithCorners.contDiffOn_extendCoordChange, ModelWithCorners.isInvertible_fderivWithin_extendCoordChange, contDiffOn_ext_coord_change, FiniteDimensional.of_locallyCompact_manifold, Manifold.locallyCompact_of_finiteDimensional]
  E1: auto
families: []
requires: [V23.C01, V16.C03, V17.C02, V17.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Extended charts

### Overview

A chart $\varphi : M \to H$ takes values in the model space, which has no linear structure. The extended chart $I \circ \varphi$ takes values in the normed space $E$, and the calculus of Volume 17 applies to it. Every definition of analysis on a manifold in Mathlib goes through extended charts: a map $f : M \to M'$ is read as $\psi \circ f \circ \varphi^{-1}$ between subsets of $E$ and $E'$, with extended charts $\varphi$ and $\psi$.

The price is that the target of an extended chart is not open when the model has a boundary. It is open in the range of $I$. So the neighbourhoods of a point of $M$ correspond to neighbourhoods within $\mathrm{range}\, I$, and derivatives in charts are derivatives within a set. This section proves the basic formulas, the smoothness and invertibility of the extended changes of charts, and the theorem of Riesz for manifolds.

### Definitions

Let $I : H \to E$ be a model with corners and $M$ a charted space over $H$.

**Definition (Extended chart).** For a chart $e$ of $M$, the *extended chart* is the partial bijection $e_I = I \circ e$ from $M$ to $E$, with source $e.\mathrm{source}$, target $I(e.\mathrm{target})$ and inverse $e^{-1} \circ I^{-1}$. The *preferred extended chart* at $x \in M$ is $\hat\varphi_x = (\varphi_x)_I$.

The extended chart is a partial bijection and not a partial homeomorphism, because its target need not be open.

::: mathlib
`extChartAt` · `Mathlib.Geometry.Manifold.IsManifold.ExtChartAt`

`e.extend I : PartialEquiv M E` is the extended chart of `e`, and `extChartAt I x = (chartAt H x).extend I`. The model `I` is an explicit argument, the space `H` is found from `I`. The basic formulas are `extChartAt_source : (extChartAt I x).source = (chartAt H x).source`, `extChartAt_target : (extChartAt I x).target = I.symm ⁻¹' (chartAt H x).target ∩ range I`, `extChartAt_coe : ⇑(extChartAt I x) = I ∘ chartAt H x` and `extChartAt_coe_symm`. The source is open (`isOpen_extChartAt_source`), and the target lies in the range of `I` (`extChartAt_target_subset_range`).

<?decl extChartAt?>
<?decl OpenPartialHomeomorph.extend?>
<?decl extChartAt_target?>
:::

**Definition (Extended change of charts).** For charts $e, e'$ of $M$, the *extended change of charts* is $\Phi_{e, e'} = e'_I \circ e_I^{-1} = I \circ e' \circ e^{-1} \circ I^{-1}$, a partial bijection of $E$ with source $I((e^{-1} \gg e').\mathrm{source})$.

**Definition (A map in extended charts).** For $f : M \to M'$ and $x \in M$, with a model $I'$ for $M'$, the map *written in extended charts* at $x$ is $\hat f_x = \hat\varphi'_{f(x)} \circ f \circ \hat\varphi_x^{-1} : E \to E'$.

::: mathlib
`ModelWithCorners.extendCoordChange` · `Mathlib.Geometry.Manifold.IsManifold.ExtChartAt`

`ModelWithCorners.extendCoordChange e e'` is the partial equivalence `(e.extend I).symm ≫ e'.extend I` of `E`, an abbreviation, with `extendCoordChange_source : (extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source`. `writtenInExtChartAt I I' x f` is the map $\hat f_x$. Chapter 4 defines the derivative `mfderiv I I' f x` as the derivative of this map within `range I` at `extChartAt I x x`.

<?decl ModelWithCorners.extendCoordChange?>
<?decl writtenInExtChartAt?>
:::

### Theorems and proofs

**Theorem (Neighbourhoods in extended charts).** Let $x \in M$ and $y = \hat\varphi_x(x)$. Then $\hat\varphi_x$ maps the neighbourhood filter $\mathcal{N}(x)$ onto the filter $\mathcal{N}_{\mathrm{range}\, I}(y)$ of neighbourhoods of $y$ within $\mathrm{range}\, I$, and $\hat\varphi_x^{-1}$ maps $\mathcal{N}_{\mathrm{range}\, I}(y)$ onto $\mathcal{N}(x)$. In particular the target of $\hat\varphi_x$ is a neighbourhood of $y$ within $\mathrm{range}\, I$. If $I$ is boundaryless, the target is open in $E$.

*Proof.* Write $\varphi = \varphi_x$. The chart $\varphi$ is a homeomorphism from the open source onto the open target, so it maps $\mathcal{N}(x)$ onto $\mathcal{N}(\varphi(x))$. By Section 1, $I$ maps $\mathcal{N}(\varphi(x))$ onto $\mathcal{N}_{\mathrm{range}\, I}(y)$. The composition gives the first claim. For the second, $\hat\varphi_x^{-1} = \varphi^{-1} \circ I^{-1}$. The map $I^{-1}$ is continuous, and its restriction to $\mathrm{range}\, I$ is the inverse of the homeomorphism $I : H \to \mathrm{range}\, I$, so it maps $\mathcal{N}_{\mathrm{range}\, I}(y)$ onto $\mathcal{N}(\varphi(x))$. Then $\varphi^{-1}$, a homeomorphism from the target onto the source, maps $\mathcal{N}(\varphi(x))$ onto $\mathcal{N}(x)$. The target $I(\varphi.\mathrm{target})$ is the image of the neighbourhood $\varphi.\mathrm{target}$ of $\varphi(x)$, so it is in $\mathcal{N}_{\mathrm{range}\, I}(y)$. If $\mathrm{range}\, I = E$, then $I$ is a homeomorphism $H \to E$, and the image of the open target is open. $\square$

**Theorem (Smoothness of extended changes of charts).** Let $M$ be a $C^n$ manifold with model $I$, and let $e, e'$ be in its maximal atlas. Then $\Phi_{e, e'}$ is $C^n$ on its source. Its source is a set of unique differentiability.

*Proof.* By Chapter 1, Section 2, $e^{-1} \gg e' \in G_n(I)$. By the definition of $G_n(I)$, $I \circ (e^{-1} \gg e') \circ I^{-1}$ is $C^n$ on $I^{-1}(s) \cap \mathrm{range}\, I$ with $s = (e^{-1} \gg e').\mathrm{source}$. This set is $I(s)$, the source of $\Phi_{e, e'}$, and the map is $\Phi_{e, e'}$. The set $I(s)$ is the intersection of $\mathrm{range}\, I$ with the open set $(I^{-1})^{-1}(s)$. Each point of a convex set with nonempty interior is a point of unique differentiability, and intersection with an open set keeps this, so $I(s)$ is a set of unique differentiability. $\square$

**Theorem (The derivative of a change of charts is invertible).** In the theorem above, assume $n \ge 1$, and let $z$ be in the source of $\Phi = \Phi_{e, e'}$, with $D$ the derivative within the source. Then $D\Phi(z)$ is an invertible continuous linear map of $E$.

*Proof.* Let $\Psi = \Phi_{e', e}$. Let $S$ be the source of $\Phi$ and $T$ its target, which is the source of $\Psi$. Both are sets of unique differentiability, $\Phi$ maps $S$ into $T$, $\Psi$ maps $T$ into $S$, $\Psi \circ \Phi = \mathrm{id}$ on $S$ and $\Phi \circ \Psi = \mathrm{id}$ on $T$. Since $n \ge 1$, $\Phi$ is differentiable within $S$ at $z$ and $\Psi$ within $T$ at $w = \Phi(z)$. The chain rule for derivatives within sets (Volume 17, Chapter 2) gives $D\Psi(w) \circ D\Phi(z) = D(\Psi \circ \Phi)(z)$, the derivative within $S$. Since $\Psi \circ \Phi$ equals the identity on $S$ and the derivative within $S$ is unique, this is $\mathrm{id}_E$. In the same way $D\Phi(z) \circ D\Psi(w) = \mathrm{id}_E$. So $D\Phi(z)$ is invertible with inverse $D\Psi(w)$. $\square$

**Theorem (Riesz for manifolds).** Let $\mathbb{K}$ be complete, and let $M$ be a nonempty charted space over $H$ with a model $I : H \to E$. If $M$ is locally compact, then $E$ is finite dimensional. Conversely, if $\mathbb{K}$ is locally compact and $E$ is finite dimensional, then $M$ is locally compact.

*Proof.* Let $x \in M$, and let $K \subseteq \varphi_x.\mathrm{source}$ be a compact neighbourhood of $x$. The map $\hat\varphi_x$ is continuous on the source, so $L = \hat\varphi_x(K)$ is compact. By the theorem on neighbourhoods, $L \in \mathcal{N}_{\mathrm{range}\, I}(y)$ with $y = \hat\varphi_x(x)$. So there is $r > 0$ with $B(y, r) \cap \mathrm{range}\, I \subseteq L$. By Section 1, $\mathrm{range}\, I$ is the closure of its interior, so there is $z \in \mathrm{int}(\mathrm{range}\, I)$ with $\|z - y\| < r$. Choose $\rho > 0$ with $\bar B(z, \rho) \subseteq B(y, r) \cap \mathrm{range}\, I$. Then $\bar B(z, \rho)$ is a closed subset of the compact set $L$, so it is compact. A normed space over a complete field with a compact ball of positive radius is finite dimensional, by the theorem of Riesz of Volume 16, Chapter 3. For the converse, $E$ is locally compact, so the closed set $\mathrm{range}\, I$ is locally compact. It is homeomorphic to $H$, and Chapter 1, Section 1 gives that $M$ is locally compact. $\square$

::: mathlib
`ModelWithCorners.isInvertible_fderivWithin_extendCoordChange` · `Mathlib.Geometry.Manifold.IsManifold.ExtChartAt`

The neighbourhood theorem is `map_extChartAt_nhds : map (extChartAt I x) (𝓝 x) = 𝓝[range I] (extChartAt I x x)` and `map_extChartAt_symm_nhdsWithin_range`, with `extChartAt_target_mem_nhdsWithin`. Under `[I.Boundaryless]`, `isOpen_extChartAt_target` and `extChartAt_target_mem_nhds`. The smoothness is `ModelWithCorners.contDiffOn_extendCoordChange`, for members of `IsManifold.maximalAtlas I n M`, and `contDiffOn_ext_coord_change` for preferred charts. The invertibility has the hypothesis `n ≠ 0` and concludes `(fderivWithin 𝕜 (extendCoordChange e e') (extendCoordChange e e').source x).IsInvertible`. The theorem of Riesz is `FiniteDimensional.of_locallyCompact_manifold`, with the converse `Manifold.locallyCompact_of_finiteDimensional`.

<?decl ModelWithCorners.isInvertible_fderivWithin_extendCoordChange?>
<?decl ModelWithCorners.contDiffOn_extendCoordChange?>
<?decl map_extChartAt_nhds?>
<?decl FiniteDimensional.of_locallyCompact_manifold?>
:::

### Examples

**Example (Normed spaces).** For the trivial model of $E$, every extended chart is the identity of $E$ (`extChartAt_model_space_eq_id`). A map $f : E \to E'$ written in extended charts is $f$.

**Example (The half line).** Let $H = [0, \infty)$, with the model $I$ of Section 1, Exercise 2, and let $M = H$ with its single chart $\mathrm{id}$. The extended chart at $x$ is the inclusion $H \to \mathbb{R}$, with target $[0, \infty)$. At $x = 0$ the target is not a neighbourhood of $0$ in $\mathbb{R}$, but it is a neighbourhood of $0$ within $[0, \infty)$. A map $f : [0, \infty) \to \mathbb{R}$ is read as the map $f \circ I^{-1} : \mathbb{R} \to \mathbb{R}$, $y \mapsto f(\max(y, 0))$. Its values for $y < 0$ carry no meaning, and derivatives are taken within $[0, \infty)$: at $0$ they are one sided.

**Example (Products).** The extended chart of $M \times M'$ at $(x, x')$ for the model $I \times I'$ is $\hat\varphi_x \times \hat\varphi'_{x'}$ (`extChartAt_prod`). Its target is the product of the targets.

**Example (The circle).** With the charts of Chapter 1, Section 1 and the trivial model of $\mathbb{R}$, the extended changes of charts are $t \mapsto 1/t$ on $\mathbb{R} \setminus \{0\}$, with derivative $-1/t^2 \neq 0$, as the theorem on invertibility says.

### The library around it

The module has many lemmas of the form "a set is a neighbourhood of $\hat\varphi_x(x)$ within $\mathrm{range}\, I$", and their names follow the pattern `extChartAt_preimage_mem_nhds`, `extChartAt_target_mem_nhdsWithin`. The lemma `uniqueDiffOn_extChartAt_target` gives the unique derivatives on the target, used in Chapter 4. The smoothness of extended changes of charts is what makes the definition of smooth maps of Chapter 3 independent of the charts. The invertibility of their derivatives gives the coordinate changes of the tangent bundle in Chapter 5, Section 3, and the independence of interior points from the chart in Section 3.

Common errors of a learner:

- Expecting `(extChartAt I x).target` to be open. It is open only under `[I.Boundaryless]`.
- Using `𝓝 (extChartAt I x x)` where `𝓝[range I] (extChartAt I x x)` is needed. The image of a neighbourhood of `x` is a neighbourhood within `range I`.
- Forgetting that `extChartAt I x` is a `PartialEquiv`, so the lemmas on `OpenPartialHomeomorph` do not apply to it directly.
- Applying the invertibility of the derivative with `n = 0`. A $C^0$ change of charts has no derivative.

### Exercises

1. (A) Prove the formula for the target of an extended chart: $\hat\varphi_x.\mathrm{target} = (I^{-1})^{-1}(\varphi_x.\mathrm{target}) \cap \mathrm{range}\, I$.
2. (A) Show that $\hat\varphi_x^{-1}(\hat\varphi_x(x)) = x$, and that $\hat\varphi_x$ is continuous on its source.
3. (A) For the half line of the example, compute the extended change of charts between the chart $\mathrm{id}$ and the chart $t \mapsto t^2$, and its derivative within the range at $0$.
4. (B) Show that if $t$ is a neighbourhood of $x$ in $M$, then $(\hat\varphi_x^{-1})^{-1}(t)$ is a neighbourhood of $\hat\varphi_x(x)$ in $E$, even if the model has a boundary. Hint: $I^{-1}$ is continuous on all of $E$.
5. (B) Let $M$ be a $C^1$ manifold with the trivial model of $\mathbb{R}^n$. Show that the Jacobian determinant of every change of charts is nonzero at every point of its source.
6. (B) Show that the chart $t \mapsto t^2$ of the half line is in the maximal atlas of $[0, \infty)$ for the $C^0$ groupoid and not for the $C^1$ groupoid.
7. (C) Show that $\ell^2$ is not the model of a locally compact manifold, and that the unit sphere of $\ell^2$ is not locally compact.

### Notes and history

The extended chart is a device of Mathlib. Texts on manifolds with boundary use charts with values in a half space and extend maps from a half space to open sets of $\mathbb{R}^n$ to define derivatives. Mathlib keeps the charts with values in $H$ and composes them with the fixed embedding $I$. The theorem of Riesz on locally compact normed spaces is from 1918.

### Reference

<?reference?>
