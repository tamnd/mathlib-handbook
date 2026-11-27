---
title: Immersions and submersions
kind: theory
modules:
  - Mathlib.Geometry.Manifold.LocalSourceTargetProperty
  - Mathlib.Geometry.Manifold.Immersion
  - Mathlib.Geometry.Manifold.ImmersionDiff
  - Mathlib.Geometry.Manifold.Submersion
explains:
  E3: [Manifold.IsImmersionAt, Manifold.IsSubmersionAt, Manifold.LiftSourceTargetPropertyAt]
  E2: [Manifold.LocalPresentationAt, Manifold.IsLocalSourceTargetProperty, Manifold.ImmersionAtProp, Manifold.SubmersionAtProp, Manifold.IsImmersionAtOfComplement, Manifold.IsImmersion, Manifold.IsSubmersion, IsOpen.isImmersionAt, isOpen_isSubmersionAt, Manifold.IsImmersionAt.isDiffImmersionAt, Manifold.IsImmersionAt.mfderiv_injective, IsDiffImmersionAt, IsDiffImmersionAt.of_injective_of_finiteDimensional, Manifold.IsImmersionAt.prodMap, ModelWithCorners.isImmersion, Manifold.IsSubmersion.id]
  E1: auto
families: []
requires: [V23.C02, V23.C03, V23.C04, V17.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Immersions and submersions

### Overview

The model maps are the inclusion $\iota(u) = (u, 0)$ of $E$ into $E \times F$ and the projection $\pi_1(u, w) = u$ of $E \times F$ onto $E$. An immersion looks like $\iota$ in suitable charts, and a submersion looks like $\pi_1$. In finite dimension the inverse function theorem of Volume 17, Chapter 6 makes these normal forms equivalent to an injective, or a surjective, differential. In infinite dimension the normal forms are stronger, and Mathlib takes them as the definitions.

Throughout, $M$ is a $C^n$ manifold modelled on $(E, H, I)$ and $N$ one modelled on $(E'', G, J)$. For a chart $\varphi$, the extended chart is $\tilde\varphi = I \circ \varphi$ (Chapter 2).

### Definitions

**Definition (Local presentation).** Let $P$ be a property of triples $(f, \varphi, \psi)$ of a map $f : M \to N$ and charts of $M$ and $N$. A *local presentation* of $f$ at $x$ for $P$ is a pair $(\varphi, \psi)$ of charts in the maximal $C^n$ atlases with $x \in \operatorname{dom}\varphi$, $f(x) \in \operatorname{dom}\psi$, $f(\operatorname{dom}\varphi) \subseteq \operatorname{dom}\psi$, and $P(f, \varphi, \psi)$. The map $f$ has the property $P$ *at* $x$ if such a presentation exists.

**Definition (Local property).** The property $P$ is *local in the source* if $P(f, \varphi, \psi)$ implies $P(f, \varphi|_U, \psi)$ for every open set $U$, and if $f = g$ on $\operatorname{dom}\varphi$ and $P(f, \varphi, \psi)$, then $P(g, \varphi, \psi)$.

**Definition (Immersion).** Let $F$ be a normed space. The map $f$ is an *immersion at $x$ with complement $F$* if it has a local presentation $(\varphi, \psi)$ at $x$ and a continuous linear isomorphism $A : E \times F \to E''$ such that
$$\tilde\psi \circ f \circ \tilde\varphi^{-1}(u) = A(u, 0) \quad \text{for all } u \in \tilde\varphi(\operatorname{dom}\varphi).$$
The map $f$ is an *immersion at $x$* if this holds for some normed space $F$, and an *immersion* if it is an immersion at every point.

**Definition (Submersion).** The map $f$ is a *submersion at $x$ with complement $F$* if it has a local presentation $(\varphi, \psi)$ at $x$ and a continuous linear isomorphism $B : E \to E'' \times F$ with
$$\tilde\psi \circ f \circ \tilde\varphi^{-1}(u) = \pi_1(B(u)) \quad \text{for all } u \in \tilde\varphi(\operatorname{dom}\varphi).$$
Submersions at $x$ and submersions are defined as for immersions.

The isomorphism $A$ hides the choice of coordinates in the target. For $E = \mathbb{R}^m$ and $E'' = \mathbb{R}^{m+k}$ one takes $F = \mathbb{R}^k$.

::: mathlib
`Manifold.LiftSourceTargetPropertyAt` · `Mathlib.Geometry.Manifold.LocalSourceTargetProperty`

The structure `LocalPresentationAt I J n f x P` holds the charts `domChart` and `codChart`, their membership in the maximal atlases, the inclusion `source_subset_preimage_source` and the proof `property`. Then `LiftSourceTargetPropertyAt` is `Nonempty` of this structure. The structure `IsLocalSourceTargetProperty P` has the fields `mono_source` and `congr`. General lemmas such as `IsOpen.liftSourceTargetPropertyAt` are proved once in this frame.

<?decl Manifold.LiftSourceTargetPropertyAt?>
<?decl Manifold.LocalPresentationAt?>
<?decl Manifold.IsLocalSourceTargetProperty?>
:::

::: mathlib
`Manifold.IsImmersionAt` · `Mathlib.Geometry.Manifold.Immersion`

The chart condition `ImmersionAtProp F I J M N f domChart codChart` asks for `equiv : (E × F) ≃L[𝕜] E''` with `(codChart.extend J) ∘ f ∘ (domChart.extend I).symm` equal to `equiv ∘ (·, 0)` on `(domChart.extend I).target`. `IsImmersionAtOfComplement F I J n f x` lifts it, and `IsImmersionAt` says that some `F` exists, in the universe of `E''`. `IsImmersion` fixes one complement for all points. No differentiability of `f` is assumed; it follows by `IsImmersionAt.contMDiffAt`.

<?decl Manifold.IsImmersionAt?>
<?decl Manifold.ImmersionAtProp?>
<?decl Manifold.IsImmersionAtOfComplement?>
<?decl Manifold.IsImmersion?>
:::

::: mathlib
`Manifold.IsSubmersionAt` · `Mathlib.Geometry.Manifold.Submersion`

The chart condition `SubmersionAtProp` asks for `equiv : E ≃L[𝕜] (E'' × F)` with the written map equal to `Prod.fst ∘ equiv`. The rest copies the immersion file. The locality lemma is `Manifold.isLocalSourceTargetProperty_submmersionAtProp`, with a double `m`.

<?decl Manifold.IsSubmersionAt?>
<?decl Manifold.SubmersionAtProp?>
<?decl Manifold.IsSubmersion?>
:::

### Theorems and proofs

**Theorem (Openness).** Let $P$ be any property of triples. The set of points $x$ at which $f$ has the property $P$ is open. In particular, the set of points where $f$ is an immersion, or a submersion, is open.

*Proof.* Let $f$ have $P$ at $x$, with the presentation $(\varphi, \psi)$. Let $y \in \operatorname{dom}\varphi$. The same pair is a presentation at $y$: $\varphi$ and $\psi$ are in the maximal atlases, $y \in \operatorname{dom}\varphi$, $f(y) \in f(\operatorname{dom}\varphi) \subseteq \operatorname{dom}\psi$, and $P(f, \varphi, \psi)$ holds. So the set contains the open neighbourhood $\operatorname{dom}\varphi$ of $x$. A set that contains a neighbourhood of each of its points is open. $\square$

**Theorem (Differential of an immersion).** Let $n \ge 1$ and let $f$ be an immersion at $x$. Then the differential $df_x : T_xM \to T_{f(x)}N$ has a continuous linear left inverse. In particular, it is injective.

*Proof.* Recall from Chapter 4 that $T_xM = E$ and that $df_x$ is the derivative, within $\operatorname{range} I$, of $f$ written in the preferred charts $\tilde\varphi_x = \operatorname{extChartAt} I\, x$ and $\tilde\psi_{f(x)}$. The map $\tau = \tilde\varphi \circ \tilde\varphi_x^{-1}$ is a change of charts of the maximal $C^n$ atlas with $n \ge 1$, so its derivative $T$ at $\tilde\varphi_x(x)$ is a continuous linear isomorphism. The same holds for $\sigma = \tilde\psi_{f(x)} \circ \tilde\psi^{-1}$ with derivative $S$. Near $\tilde\varphi_x(x)$ in $\operatorname{range} I$,
$$\tilde\psi_{f(x)} \circ f \circ \tilde\varphi_x^{-1} = \sigma \circ (\tilde\psi \circ f \circ \tilde\varphi^{-1}) \circ \tau = \sigma \circ A \circ \iota \circ \tau.$$
The chain rule gives $df_x = S \circ A \circ \iota \circ T$. Put $L = T^{-1} \circ \pi_1 \circ A^{-1} \circ S^{-1}$. Then $L \circ df_x = T^{-1} \circ \pi_1 \circ \iota \circ T = \mathrm{id}_E$, because $\pi_1 \circ \iota = \mathrm{id}_E$. It is continuous linear, and a map with a left inverse is injective. $\square$

The hypothesis $n \ge 1$ is needed: for $n = 0$ a change of charts can have no derivative. Example 3 shows a $C^0$ immersion with zero differential.

**Theorem (Submersions have surjective differential).** Let $n \ge 1$ and let $f$ be a submersion at $x$. Then $df_x$ has a continuous linear right inverse. In particular, it is surjective.

*Proof.* With the notation of the previous proof, $df_x = S \circ \pi_1 \circ B \circ T$. Let $j(e) = (e, 0)$ from $E''$ to $E'' \times F$ and put $R = T^{-1} \circ B^{-1} \circ j \circ S^{-1}$. Then $df_x \circ R = S \circ \pi_1 \circ j \circ S^{-1} = \mathrm{id}_{E''}$. $\square$

The index of this edition has no declaration for this theorem: there is no lemma that the differential of a submersion is surjective.

**Theorem (Injective differential gives an immersion).** Let $M$ and $N$ be manifolds without boundary of finite dimensions $m$ and $m + k$ over $\mathbb{R}$, of class $C^n$ with $n \ge 1$. Let $f : M \to N$ be $C^n$ near $x$, with $df_x$ injective. Then $f$ is an immersion at $x$ with complement $\mathbb{R}^k$.

*Proof.* Choose charts $\varphi$ at $x$ and $\psi$ at $f(x)$ with values in $\mathbb{R}^m$ and $\mathbb{R}^{m+k}$, and shrink $\varphi$ so that $f(\operatorname{dom}\varphi) \subseteq \operatorname{dom}\psi$. Let $g = \psi \circ f \circ \varphi^{-1}$ on the open set $U = \varphi(\operatorname{dom}\varphi)$, and $a = \varphi(x)$. Then $Dg(a)$ is injective, as it differs from $df_x$ by isomorphisms, so its image $L$ has dimension $m$. Choose $W$ with $\mathbb{R}^{m+k} = L \oplus W$ and an isomorphism $C : \mathbb{R}^k \to W$. Define
$$\Phi : U \times \mathbb{R}^k \to \mathbb{R}^{m+k}, \quad \Phi(u, w) = g(u) + C w.$$
Then $\Phi$ is $C^n$ and $D\Phi(a, 0)(h, w) = Dg(a)h + Cw$. If $Dg(a)h + Cw = 0$, then $Dg(a)h = 0$ and $Cw = 0$ since $L \cap W = 0$, so $h = 0$ and $w = 0$. An injective linear map between spaces of dimension $m + k$ is an isomorphism. By the inverse function theorem (Volume 17, Chapter 6), there are open sets $\Omega \ni (a, 0)$ and $V \ni g(a)$ such that $\Phi : \Omega \to V$ is a $C^n$ diffeomorphism.

Let $A : \mathbb{R}^m \times \mathbb{R}^k \to \mathbb{R}^{m+k}$ be the standard identification and put $\psi' = A \circ \Phi^{-1} \circ \psi$ on $\psi^{-1}(V)$. Its changes of charts with $\psi$ are $A \circ \Phi^{-1}$ and $\Phi \circ A^{-1}$, which are $C^n$, so $\psi'$ is in the maximal $C^n$ atlas. Let $U' = \{u \in U : (u, 0) \in \Omega\}$, an open set that contains $a$, and $\varphi' = \varphi|_{\varphi^{-1}(U')}$. For $u \in U'$, the point $g(u) = \Phi(u, 0)$ lies in $V$, so $f(\operatorname{dom}\varphi') \subseteq \operatorname{dom}\psi'$, and
$$\psi' \circ f \circ \varphi'^{-1}(u) = A\,\Phi^{-1}(g(u)) = A\,\Phi^{-1}(\Phi(u, 0)) = A(u, 0).$$
This is the normal form. $\square$

The proof uses a complement $W$, which a Banach space need not have, the count of dimensions, and the absence of boundary. The submersion analogue is Exercise 4.

::: mathlib
`IsDiffImmersionAt` · `Mathlib.Geometry.Manifold.ImmersionDiff`

`IsDiffImmersionAt I J f x` is `(mfderiv I J f x).HasLeftInverse`. The theorem on the differential is `IsImmersionAt.isDiffImmersionAt`, with `n ≠ 0`, and `IsImmersionAt.mfderiv_injective` gives injectivity. In finite dimension, `IsDiffImmersionAt.of_injective_of_finiteDimensional` turns an injective differential into a left inverse. The step from `IsDiffImmersionAt` to `IsImmersionAt` is a TODO of the file: the index of this edition has no declaration for it.

<?decl IsDiffImmersionAt?>
<?decl Manifold.IsImmersionAt.isDiffImmersionAt?>
<?decl Manifold.IsImmersionAt.mfderiv_injective?>
<?decl IsDiffImmersionAt.of_injective_of_finiteDimensional?>
:::

### Examples

**Example (Linear inclusions and projections).** The map $f(u) = (u, 0)$ from $\mathbb{R}^m$ to $\mathbb{R}^{m+k}$ is an immersion with complement $\mathbb{R}^k$: take identity charts. The projection $p(u, w) = u$ is a submersion. A model with corners $I : H \to E$, seen as a map of manifolds, is an immersion; for a half-space $H$ this includes the boundary points.

**Example (The circle).** For $\gamma(t) = (\cos t, \sin t)$ the derivative $\gamma'(t) = (-\sin t, \cos t)$ is nonzero, so $\gamma$ is an immersion by the theorem above. The proof gives explicit charts: at $t = 0$ take $W = \mathbb{R}(1, 0)$ and $\Phi(t, w) = ((1 + w)\cos t, (1+w)\sin t)$. Then $\Phi^{-1}$ is a polar chart near $(1, 0)$, and in it $\gamma$ reads $t \mapsto (t, 0)$. The map $\gamma$ is not injective, and an immersion need not be.

**Example (A $C^0$ immersion with zero differential).** Let $f : \mathbb{R} \to \mathbb{R}$, $f(t) = t^3$. As a $C^\infty$ map, $f'(0) = 0$, so $f$ is not a $C^1$ immersion at $0$. But $f$ is a homeomorphism, so $\psi = f^{-1}$ is a chart of the $C^0$ maximal atlas of $\mathbb{R}$, and $\psi \circ f = \mathrm{id}$. So $f$ is an immersion of class $C^0$ at every point. This is the reason for $n \ne 0$ in the theorem on the differential.

### The library around it

The files `Immersion` and `Submersion` build the same list: openness, products (`prodMap`), restriction to open subsets (`of_opens`), local change of the map (`congr_of_eventuallyEq`), change of complement (`congr_F`, `trans_F`) and smoothness (`contMDiffAt`). `IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt` builds an immersion from the normal form in the preferred charts. `IsDiffImmersionAt.comp` composes the differential version; the composition of immersions is a TODO. The docstring of `IsDiffImmersionAt` says that the two notions agree under mild conditions, differ in general (with counterexamples involving boundary), and that the equivalence is not yet proved.

::: mathlib
`ModelWithCorners.isImmersion` · `Mathlib.Geometry.Manifold.Immersion`

`ModelWithCorners.isImmersion` says `IsImmersion I 𝓘(𝕜, E) n I` for a natural number `n`. `IsSubmersion.id` covers the identity. `IsImmersionAt.prodMap` needs `IsManifold` on all four manifolds.

<?decl ModelWithCorners.isImmersion?>
<?decl Manifold.IsSubmersion.id?>
<?decl Manifold.IsImmersionAt.prodMap?>
<?decl IsOpen.isImmersionAt?>
<?decl isOpen_isSubmersionAt?>
:::

Common errors of a learner:

- Expecting `IsImmersionAt` to imply an injective `mfderiv` without the hypothesis `n ≠ 0`. Example 3 is a counterexample at order $0$.
- Looking for a lemma that the differential of a submersion is surjective. The index of this edition has no such declaration. Unfold `SubmersionAtProp`.

### Exercises

1. (A) Show that $t \mapsto (t^2, t^3)$ from $\mathbb{R}$ to $\mathbb{R}^2$ is an immersion at every $t \ne 0$ and is not a $C^1$ immersion at $0$. Hint: compute the derivative.
2. (A) Show that $h(x, y) = x^2 - y^2$ from $\mathbb{R}^2$ to $\mathbb{R}$ is a submersion at every point other than the origin, and is not a $C^1$ submersion at the origin. Hint: use Exercise 4 and the theorem on the differential of a submersion.
3. (B) Let $f : M \to N$ and $g : M' \to N'$ be immersions at $x$ and $x'$. Prove that $f \times g$ is an immersion at $(x, x')$, with complement $F \times F'$. Hint: use product charts and reorder the factors of $E \times E' \times F \times F'$.
4. (B) Prove the analogue of the theorem on injective differentials for submersions: in finite dimension without boundary, if $df_x$ is surjective, then $f$ is a submersion at $x$. Hint: let $K = \ker Dg(a)$, choose a linear map $Q : \mathbb{R}^{m} \to K$ that is the identity on $K$, and apply the inverse function theorem to $u \mapsto (g(u), Q u)$.
5. (C) In finite dimension without boundary, prove that the composite of two immersions is an immersion. Hint: use the theorem on injective differentials and the chain rule.
6. (C) Let $E''$ be a Banach space and $L \subseteq E''$ a closed subspace with no closed complement. Show that the inclusion $L \to E''$ has an injective differential but is not an immersion. Hint: an immersion has a differential with a continuous left inverse $P$, and then $\ker P$ is a closed complement of $L$.

### Notes and history

The normal forms in finite dimension are forms of the rank theorem. The Mathlib file on immersions cites Margalef-Roig and Outerelo Dominguez, *Differential topology*, for the definition on Banach manifolds, and the file on submersions cites Schmeding, *An introduction to infinite-dimensional differential geometry*.

### Reference

<?reference?>
