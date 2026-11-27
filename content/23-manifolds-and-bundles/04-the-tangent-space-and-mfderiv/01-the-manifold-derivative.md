---
title: The manifold derivative
kind: theory
modules:
  - Mathlib.Geometry.Manifold.MFDeriv.Defs
  - Mathlib.Geometry.Manifold.MFDeriv.Basic
  - Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
explains:
  E3: [mfderiv, MDifferentiableAt, HasMFDerivAt]
  E2: [MDifferentiableWithinAt, HasMFDerivWithinAt, mfderivWithin, MDifferentiable, UniqueMDiffWithinAt, UniqueMDiffOn, tangentMap, tangentMapWithin, mdifferentiableAt_iff, MDifferentiableAt.continuousAt, mfderiv_zero_of_not_mdifferentiableAt, MDifferentiableAt.hasMFDerivAt, HasMFDerivAt.mfderiv, UniqueMDiffWithinAt.eq, uniqueMDiffWithinAt_univ, uniqueMDiffOn_univ, IsOpen.uniqueMDiffOn, mfderivWithin_eq_mfderiv, HasMFDerivAt.comp, HasMFDerivWithinAt.comp, mfderiv_comp, MDifferentiableAt.comp, tangentMap_comp, writtenInExtChartAt_comp, ContMDiffAt.mdifferentiableAt, ContMDiff.mdifferentiable, mdifferentiableWithinAt_iff_of_mem_source, OpenPartialHomeomorph.MDifferentiable, UniqueMDiffOn.uniqueMDiffOn_preimage, UniqueMDiffOn.uniqueDiffOn_target_inter]
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


## The manifold derivative

### Overview

A map $f : M \to M'$ between manifolds has no derivative in the sense of Volume 17, because $M$ and $M'$ are not vector spaces. Written in a chart at $x$ and a chart at $f(x)$, $f$ becomes a map between parts of model vector spaces, and its Fréchet derivative is the derivative of $f$ at $x$.

This section defines the tangent space, `mfderiv` and the tangent map, and proves the basic facts and the chain rule.

### Definitions

Fix a nontrivially normed field $\Bbbk$, models with corners $I$ on $(E, H)$, $I'$ on $(E', H')$ and $I''$ on $(E'', H'')$, and charted spaces $M$, $M'$, $M''$ over $H$, $H'$, $H''$. For $x \in M$ let $\varphi_x$ be the extended chart `extChartAt I x` of Chapter 2, Section 2. Its source is the source of the preferred chart at $x$, an open neighbourhood of $x$, and its values lie in $R = \operatorname{range} I$. Write $R' = \operatorname{range} I'$.

**Definition (Tangent space).** The tangent space of $M$ at $x$ is the vector space $T_xM = E$.

An element of $T_xM$ is a tangent vector written in the coordinates of the preferred chart at $x$. With this choice the derivative of $f$ at $x$ is a continuous linear map $E \to E'$, and no new space must be constructed.

**Definition (Map written in charts).** For $f : M \to M'$ and $x \in M$, the map $f$ written in the preferred charts at $x$ is
$$f_x = \varphi'_{f(x)} \circ f \circ \varphi_x^{-1} : E \to E',$$
where $\varphi'_{f(x)}$ is the extended chart of $M'$ at $f(x)$. Mathlib calls it `writtenInExtChartAt I I' x f`.

**Definition (Derivative of a map between manifolds).** Let $L : E \to E'$ be continuous linear and $s \subseteq M$.

1. $f$ has derivative $L$ at $x$ if $f$ is continuous at $x$ and $f_x$ has Fréchet derivative $L$ at $\varphi_x(x)$ within $R$.
2. $f$ has derivative $L$ at $x$ within $s$ if $f$ is continuous at $x$ within $s$ and $f_x$ has derivative $L$ at $\varphi_x(x)$ within $\varphi_x^{-1}(s) \cap R$, where $\varphi_x^{-1}(s)$ is the preimage of $s$ under $\varphi_x^{-1} : E \to M$.
3. $f$ is differentiable at $x$, or within $s$ at $x$, if it has some derivative there.

The derivative in charts is taken within $R$. When $M$ has a boundary, $R$ is a half-space, and only the values of $f_x$ on $R$ have a meaning.

**Definition (mfderiv).** If $f$ is differentiable at $x$, then $Df(x) = $ `mfderiv I I' f x` is the derivative `fderivWithin` of $f_x$ at $\varphi_x(x)$ within $R$. Otherwise it is $0$. The map `mfderivWithin I I' f s x` uses the set $\varphi_x^{-1}(s) \cap R$ in the same way.

**Definition (Unique differentials).** A set $s \subseteq M$ has unique differentials at $x$ if $\varphi_x^{-1}(s) \cap R$ has unique differentials at $\varphi_x(x)$ in the sense of Volume 17: its tangent cone spans a dense subspace of $E$.

**Definition (Tangent map).** The tangent map of $f$ sends a pair $(x, v)$ with $v \in T_xM$ to $(f(x), Df(x)v)$. It acts between the tangent bundles of Chapter 5.

::: mathlib
`mfderiv` · `Mathlib.Geometry.Manifold.MFDeriv.Defs`

`MDifferentiableWithinAt I I' f s x` is `LiftPropWithinAt` of a property in charts, a local invariant property in the sense of Chapter 1. The lemma `mdifferentiableAt_iff` unfolds it to continuity and differentiability of `writtenInExtChartAt I I' x f` within `range I`. `TangentSpace I x` is defined in Chapter 2 to be `E`, with its topology and vector structure but without its norm. `HasMFDerivAt` composes $L$ with `tangentSpaceCastModel`, the identity of `E` seen as a map from `TangentSpace I x`, so that the types match. The notation of Chapter 3 writes `mfderiv% f x` and `MDiffAt f x`.

<?decl TangentSpace?>
<?decl MDifferentiableAt?>
<?decl HasMFDerivAt?>
<?decl mfderiv?>
<?decl UniqueMDiffWithinAt?>
<?decl tangentMap?>
:::

### Theorems and proofs

**Theorem (Differentiable maps are continuous).** If $f$ is differentiable at $x$, then $f$ is continuous at $x$.

*Proof.* Continuity at $x$ is part of the definition. $\square$

Without this condition, $f$ could send points near $x$ outside the chart at $f(x)$, where $f_x$ has arbitrary values.

**Theorem (Uniqueness of the derivative).** Let $s$ have unique differentials at $x$. If $f$ has derivatives $L_1$ and $L_2$ at $x$ within $s$, then $L_1 = L_2$. If $f$ is differentiable at $x$, then $Df(x)$ is its only derivative at $x$.

*Proof.* Put $t = \varphi_x^{-1}(s) \cap R$ and $a = \varphi_x(x)$. Both $L_i$ are derivatives of $f_x$ at $a$ within $t$, and by Volume 17 a derivative within a set with unique differentials is unique. For the second claim take $s = M$, so that $t = R$. The range of a model with corners has unique differentials at each of its points; this is one of the axioms of Chapter 2. If $f_x$ is differentiable within $R$ at $a$, then `fderivWithin` is a derivative there, so $Df(x)$ is a derivative of $f$, and it is the only one. $\square$

For an open set $U$ and $x \in U$, the set $\varphi_x^{-1}(U) \cap R$ agrees with $R$ near $\varphi_x(x)$, because $\varphi_x^{-1}$ is continuous at that point. So open sets have unique differentials, and derivatives within $U$ are derivatives at $x$.

**Theorem (Chain rule).** Let $f : M \to M'$ have derivative $A$ at $x$ and $g : M' \to M''$ have derivative $B$ at $f(x)$. Then $g \circ f$ has derivative $B \circ A$ at $x$. If $f$ is differentiable at $x$ and $g$ at $f(x)$, then
$$D(g \circ f)(x) = Dg(f(x)) \circ Df(x).$$

*Proof.* Write $\varphi = \varphi_x$, $\psi = \varphi'_{f(x)}$, $\chi = \varphi''_{g(f(x))}$, $a = \varphi(x)$ and $b = \psi(f(x))$. By hypothesis $f$ is continuous at $x$, $g$ is continuous at $f(x)$, $f_x = \psi \circ f \circ \varphi^{-1}$ has derivative $A$ at $a$ within $R$, and $g_{f(x)} = \chi \circ g \circ \psi^{-1}$ has derivative $B$ at $b$ within $R'$.

Step 1. The map $g \circ f$ is continuous at $x$.

Step 2. The values of $\psi$ lie in $R'$, so $f_x$ maps $R$ into $R'$. Since $x$ is in the source of $\varphi$, $\varphi^{-1}(a) = x$ and $f_x(a) = b$. By the chain rule within sets of Volume 17, $g_{f(x)} \circ f_x$ has derivative $B \circ A$ at $a$ within $R$.

Step 3. Let $W$ be the set of $y \in R$ with $z = f(\varphi^{-1}(y))$ in the source of $\psi$. For $y \in W$, $\psi^{-1}(\psi(z)) = z$, so
$$g_{f(x)}(f_x(y)) = \chi(g(\psi^{-1}(\psi(z)))) = \chi(g(z)) = (g \circ f)_x(y).$$
The source of $\psi$ is an open neighbourhood of $f(x)$, and $f$ is continuous at $x$. The map $\varphi^{-1}$ is continuous at $a$ with $\varphi^{-1}(a) = x$. So $W$ is a neighbourhood of $a$ within $R$ that contains $a$. A derivative within $R$ depends only on the values on such a set, so $(g \circ f)_x$ has derivative $B \circ A$ at $a$ within $R$. With Step 1 this is the first claim.

The formula follows: by uniqueness $Df(x)$ and $Dg(f(x))$ are derivatives, so $Dg(f(x)) \circ Df(x)$ is a derivative of $g \circ f$, and by uniqueness again it is $D(g \circ f)(x)$. $\square$

The proof uses only the preferred charts, and the chart $\psi$ cancels. So Mathlib proves the chain rule without the class `IsManifold`. The version within sets needs $s \subseteq f^{-1}(u)$, and the formula for `mfderivWithin` needs unique differentials of $s$ at $x$.

**Theorem ($C^n$ maps are differentiable).** Let $n \ge 1$ in `WithTop ℕ∞`. If $f$ is $C^n$ at $x$, then $f$ is differentiable at $x$.

*Proof.* By Chapter 3, $f$ is $C^n$ at $x$ if and only if $f$ is continuous at $x$ and $f_x$ is $C^n$ within $R$ at $\varphi_x(x)$. By Volume 17, a map that is $C^n$ within a set at a point, with $n \ge 1$, is differentiable within the set at the point. $\square$

**Theorem (Independence of the charts).** Let $M$ and $M'$ be manifolds of class $C^1$. Let $x'$ lie in the source of the chart at $x \in M$, and $f(x')$ in the source of the chart at $y \in M'$. Then $f$ is differentiable at $x'$ if and only if $f$ is continuous at $x'$ and $h = \varphi'_y \circ f \circ \varphi_x^{-1}$ is differentiable within $R$ at $a = \varphi_x(x')$.

*Proof.* Both sides contain continuity of $f$ at $x'$. Let $\tau = \varphi_{x'} \circ \varphi_x^{-1}$ and $\tau' = \varphi'_y \circ (\varphi'_{f(x')})^{-1}$. Since the manifolds are of class $C^1$, the changes of charts lie in `contDiffGroupoid 1`, so $\tau$, $\tau'$ and their inverses are $C^1$ within the ranges on their domains, which are neighbourhoods within the ranges. They map $R$ into $R$ and $R'$ into $R'$. As in Step 3 of the chain rule, continuity of $f$ at $x'$ gives a neighbourhood of $a$ within $R$ on which $h = \tau' \circ f_{x'} \circ \tau$, with equality at $a$. If $f_{x'}$ is differentiable within $R$ at $\tau(a)$, the chain rule within sets, applied twice, shows that $h$ is differentiable within $R$ at $a$. Conversely, $f_{x'} = (\tau')^{-1} \circ h \circ \tau^{-1}$ near $\tau(a)$. $\square$

This is where `IsManifold` enters. Mathlib states the theorem as `mdifferentiableWithinAt_iff_of_mem_source` with `IsManifold I 1 M` and `IsManifold I' 1 M'`.

### Examples

**Example (Maps between normed spaces).** Let $M = E$ and $M' = E'$ with the trivial models. Every extended chart is the identity, so $f_x = f$ and $R = E$. So $Df(x)$ is the Fréchet derivative, since Fréchet differentiable maps are continuous. Section 2 gives the Mathlib form.

**Example (The junk value).** Let $f(t) = |t|$ on $\mathbb{R}$. It is not differentiable at $0$, so `mfderiv` of $f$ at $0$ is $0$, although $0$ is not a derivative of $f$ at $0$.

**Example (A point of the boundary).** Let $M = [0, \infty)$ with the model of the half-line, so that $R = [0, \infty)$ and the charts are inclusions. Let $f(t) = t^2 + 3t$, with values in $\mathbb{R}$. At $0$ the difference quotients along $R$ are $(h^2 + 3h)/h = h + 3 \to 3$ for $h \to 0^+$. So $f$ has derivative $v \mapsto 3v$ within $R$. The tangent cone of $R$ at $0$ is $[0, \infty)$, which spans $\mathbb{R}$, so the derivative is unique. It is defined on all of $T_0M = \mathbb{R}$, also on the vectors $v < 0$ that point out of $M$.

**Example (A set without unique differentials).** Let $s = \mathbb{R} \times \{0\} \subseteq \mathbb{R}^2$ and $f(u, w) = uw$. For each $c \in \mathbb{R}$, the map $L_c(h, k) = ck$ is a derivative of $f$ at $0$ within $s$, because $f$ and $L_c$ both vanish on $s$. The tangent cone of $s$ at $0$ is the line $s$, which does not span $\mathbb{R}^2$. The value of `mfderivWithin` within $s$ is one of these maps, chosen by the definition, and no lemma identifies it.

### The library around it

The definitions are in `Mathlib.Geometry.Manifold.MFDeriv.Defs` and the general lemmas in `Mathlib.Geometry.Manifold.MFDeriv.Basic`. Each lemma comes in the forms at a point, within a set, on a set and everywhere, with the prefixes `MDifferentiableAt`, `MDifferentiableWithinAt`, `MDifferentiableOn` and `MDifferentiable`.

::: mathlib
`HasMFDerivAt.comp` · `Mathlib.Geometry.Manifold.MFDeriv.Basic`

The chain rule is `HasMFDerivAt.comp` in the predicate form and `mfderiv_comp` as a formula, which needs `MDifferentiableAt` of both maps. Step 3 of the proof is `writtenInExtChartAt_comp`, and `tangentMap_comp` is the chain rule for tangent maps. `MDifferentiableAt.hasMFDerivAt` and `HasMFDerivAt.mfderiv` pass between the two forms. `ContMDiff.mdifferentiable` takes the hypothesis `n ≠ 0`, which is $n \ge 1$.

<?decl HasMFDerivAt.comp?>
<?decl mfderiv_comp?>
<?decl MDifferentiableAt.continuousAt?>
<?decl ContMDiff.mdifferentiable?>
<?decl mdifferentiableWithinAt_iff_of_mem_source?>
:::

The file `Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential` carries unique differentials along maps $e$ with `OpenPartialHomeomorph.MDifferentiable I I' e`, which says that $e$ and its inverse are differentiable on the source and the target.

Common errors of a learner:

- Using a fact about `mfderiv f x` without a proof of `MDifferentiableAt`. The value is then $0$, and `mfderiv_comp` do not apply.
- Expecting a norm on `TangentSpace I x`. Use `tangentSpaceCastModel`, or work in $E$.
- Forgetting `range I`. For a boundaryless model (`ModelWithCorners.Boundaryless`), `ModelWithCorners.range_eq_univ` of Chapter 2 replaces it by $E$.

### Exercises

1. (A) Prove from the definition that a constant map has derivative $0$ at each point. Hint: the written map is constant near $\varphi_x(x)$.
2. (A) Prove that the identity of $M$ has derivative $\mathrm{id}_E$ at each point. Hint: $\varphi_x \circ \varphi_x^{-1}$ is the identity on the target of $\varphi_x$.
3. (B) Prove the chain rule within sets: if $f$ has derivative $A$ at $x$ within $s$, $g$ has derivative $B$ at $f(x)$ within $u$, and $s \subseteq f^{-1}(u)$, then $g \circ f$ has derivative $B \circ A$ at $x$ within $s$. Hint: check that $f_x$ maps $\varphi_x^{-1}(s) \cap R$ into $\psi^{-1}(u) \cap R'$ near $\varphi_x(x)$.
4. (B) Let $s$ and $t$ have unique differentials at $x$ and $y$. Prove that $s \times t$ has unique differentials at $(x, y)$. Hint: the extended chart of a product is the product of the extended charts.
5. (B) Give a map $f : \mathbb{R} \to \mathbb{R}$ with `mfderiv f 0 = 0` that is not differentiable at $0$, and one that is. Explain why the equation alone does not decide between them.
6. (C) Let $M$ be of class $C^1$ and $e$ a chart of its atlas. Prove that $e : M \to H$, with the model $I$ on $H$, is differentiable on its source. Hint: apply the independence of the charts with the chart $e$ at the source.

### Notes and history

Classical texts define a tangent vector as a class of coordinate vectors that transform by the derivative of the change of charts. Mathlib keeps the vector in the preferred chart and moves the rule into the tangent bundle of Chapter 5. The file headers of `Mathlib.Geometry.Manifold.MFDeriv.Defs` and `Mathlib.Geometry.Manifold.MFDeriv.Basic` name Sébastien Gouëzel and Floris van Doorn as authors.

### Reference

<?reference?>
