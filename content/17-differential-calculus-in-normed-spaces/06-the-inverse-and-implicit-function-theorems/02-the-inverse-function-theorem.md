---
title: The inverse function theorem
kind: theory
modules:
  - Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
  - Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
  - Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
  - Mathlib.Analysis.Calculus.InverseFunctionTheorem.FiniteDimensional
explains:
  E3: [HasStrictFDerivAt.toOpenPartialHomeomorph, HasStrictFDerivAt.localInverse, HasStrictFDerivAt.to_localInverse, ContDiffAt.to_localInverse]
  E2: [HasStrictFDerivAt.approximates_deriv_on_nhds, HasStrictFDerivAt.map_nhds_eq_of_surj, HasStrictFDerivAt.to_local_left_inverse, HasStrictFDerivAt.eventually_left_inverse, HasStrictFDerivAt.eventually_right_inverse, HasStrictFDerivAt.localInverse_unique, ContDiffAt.toOpenPartialHomeomorph, ContDiffAt.localInverse, HasStrictDerivAt.localInverse, HasStrictDerivAt.to_localInverse, isOpenMap_of_hasStrictDerivAt, ApproximatesLinearOn.exists_homeomorph_extension]
  E1: auto
families: []
requires: [V17.C01, V17.C02, V17.C03, V17.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The inverse function theorem

### Overview

A linear map $A$ is invertible when the equation $A x = y$ has exactly one solution for each $y$. The inverse function theorem transfers this to a nonlinear map $f$ near a point $a$: if $Df(a)$ is invertible, then $f(x) = y$ has exactly one solution $x$ near $a$ for each $y$ near $f(a)$, and the solution depends on $y$ as smoothly as $f$ depends on $x$. The theorem is local.

The proof has two steps. Strict differentiability at $a$ makes $f$ approximately linear on a small ball, in the sense of Section 1, so $f$ is a homeomorphism of the ball onto an open set. Then a short computation gives the derivative of the inverse, and an induction gives the $C^k$ version. As in Section 1, $E$ and $F$ are Banach spaces over $\mathbb{K}$, $A : E \to F$ is a continuous linear equivalence and $N = \|A^{-1}\|$.

### Definitions

Recall from Chapter 3 that $f$ is *strictly differentiable* at $a$ with the derivative $A$ if
$$\frac{\|f(x) - f(y) - A(x - y)\|}{\|x - y\|} \to 0 \quad \text{as } (x, y) \to (a, a),\ x \ne y.$$
Chapter 3 proves that every $C^1$ map is strictly differentiable at each point.

**Definition (Local inverse).** Let $f : E \to F$ and $a \in E$. A *local inverse* of $f$ at $a$ is a map $g : F \to E$ with open sets $U \ni a$ and $V \ni f(a)$ such that $f$ maps $U$ bijectively onto $V$, $g$ maps $V$ onto $U$, and $g(f(x)) = x$ for $x \in U$ and $f(g(y)) = y$ for $y \in V$. If in addition $f$ and $g$ are continuous on $U$ and $V$, the pair is a homeomorphism of $U$ onto $V$.

### Theorems and proofs

**Lemma (Strict derivatives give approximate linearity).** Let $f$ be strictly differentiable at $a$ with the derivative $A$. For each $c > 0$ there is $\delta > 0$ such that $f$ approximates $A$ on the open ball $B(a, \delta)$ with the constant $c$.

*Proof.* By the definition there is $\delta > 0$ with $\|f(x) - f(y) - A(x - y)\| \le c\|x - y\|$ when $x, y \in B(a, \delta)$ and $x \ne y$. For $x = y$ both sides are $0$. $\square$

::: mathlib
`HasStrictFDerivAt.approximates_deriv_on_nhds` · `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`

From `HasStrictFDerivAt f f' a` and `Subsingleton E ∨ 0 < c`, it gives `∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c`.

<?decl HasStrictFDerivAt.approximates_deriv_on_nhds?>
:::

**Theorem (Inverse function theorem).** Let $f : E \to F$ be strictly differentiable at $a$, with an invertible derivative $A = Df(a)$. Then there are open sets $U \ni a$ and $V \ni f(a)$ such that $f$ is a homeomorphism of $U$ onto $V$. The inverse $g : V \to U$ is strictly differentiable at $f(a)$, with
$$Dg(f(a)) = A^{-1}.$$

*Proof.* Take $c = 1/(2N)$, so $N^{-1} - c = 1/(2N)$. The lemma gives an open ball $U = B(a, \delta)$ on which $f$ approximates $A$ with the constant $c$. By Section 1, $V = f(U)$ is open, $f$ is a homeomorphism of $U$ onto $V$, and $g$ is Lipschitz with the constant $2N$.

For the derivative, let $y, y' \in V$ and $x = g(y)$, $x' = g(y')$. Then $y - y' = f(x) - f(x')$, and
$$g(y) - g(y') - A^{-1}(y - y') = A^{-1}\big(A(x - x') - f(x) + f(x')\big) = -A^{-1}\big(f(x) - f(x') - A(x - x')\big).$$
Let $\varepsilon > 0$. By strict differentiability, there is $\eta > 0$ with $\|f(x) - f(x') - A(x - x')\| \le \varepsilon\|x - x'\|$ for $x, x' \in B(a, \eta)$. Since $g$ is continuous at $f(a)$ and $g(f(a)) = a$, there is $\rho > 0$ with $g(B(f(a), \rho)) \subseteq B(a, \eta)$. For $y, y' \in B(f(a), \rho) \cap V$,
$$\|g(y) - g(y') - A^{-1}(y - y')\| \le N\varepsilon\|x - x'\| \le N\varepsilon \cdot 2N\|y - y'\|.$$
Since $\varepsilon$ is arbitrary, $g$ is strictly differentiable at $f(a)$ with the derivative $A^{-1}$. $\square$

The same lines prove a pointwise statement. If $g$ is $L$-Lipschitz on $V$, $f(g(z)) = z$ on $V$, and $f$ is differentiable at $g(y)$ with an invertible derivative $B$, then $g$ is differentiable at $y$ with $Dg(y) = B^{-1}$. Use $x' = g(y)$ fixed in the display above, and $\|x - x'\| \le L\|z - y\|$.

::: mathlib
`HasStrictFDerivAt.toOpenPartialHomeomorph` · `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`

The call is `hf.toOpenPartialHomeomorph f` for `hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a` with `f' : E ≃L[𝕜] F` and `[CompleteSpace E]`. The result is an `OpenPartialHomeomorph E F` whose forward map is `f` and whose source contains `a`. Mathlib does not ask for `CompleteSpace F`: the equivalence `f'` makes `F` complete. The open source is the set of Section 1, built by `ApproximatesLinearOn.toOpenPartialHomeomorph`.

<?decl HasStrictFDerivAt.toOpenPartialHomeomorph?>
:::

::: mathlib
`HasStrictFDerivAt.localInverse` · `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`

`HasStrictFDerivAt.localInverse f f' a hf : F → E` is the inverse map of the open partial homeomorphism. It is a total function. Its values far from `f a` mean nothing, and the theorems about it hold eventually near `f a`: `HasStrictFDerivAt.eventually_left_inverse` says `∀ᶠ x in 𝓝 a, localInverse f f' a hf (f x) = x`, and `eventually_right_inverse` is the other composition. `HasStrictFDerivAt.localInverse_unique` says that any `g` with `g (f x) = x` near `a` agrees with the local inverse near `f a`.

<?decl HasStrictFDerivAt.localInverse?>
:::

::: mathlib
`HasStrictFDerivAt.to_localInverse` · `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`

It states `HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm : F →L[𝕜] E) (f a)`, the derivative formula of the theorem. In a proof, `HasStrictFDerivAt.to_local_left_inverse` is often handier: it gives the same derivative for any `g` with `∀ᶠ x in 𝓝 a, g (f x) = x`, so a formula for the inverse can be used directly.

<?decl HasStrictFDerivAt.to_localInverse?>
:::

The surjective form needs only $A$ onto, not invertible. By the open mapping theorem of Volume 16, $A$ then has a bounded nonlinear right inverse, and the theorem on balls of Section 1 shows that $f$ maps each neighbourhood of $a$ onto a neighbourhood of $f(a)$. Mathlib states this as `HasStrictFDerivAt.map_nhds_eq_of_surj`: the image of the filter `𝓝 a` is `𝓝 (f a)`.

**Theorem (Smooth inverse function theorem).** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and $1 \le k \le \infty$. Let $f$ be $C^k$ on a neighbourhood of $a$, with $Df(a)$ invertible. Then the local inverse $g$ is $C^k$ on a neighbourhood of $f(a)$, and $Dg(y) = Df(g(y))^{-1}$ there.

*Proof.* A $C^1$ map is strictly differentiable, so the inverse function theorem applies and gives $U$, $V$ and a Lipschitz $g$. The invertible maps form an open subset of $L(E, F)$ (Volume 16), and $Df$ is continuous. Shrink $U$ to a ball on which $Df(x)$ is invertible and $f$ is $C^k$, and replace $V$ by $f(U)$. For $y \in V$, the pointwise statement after the proof gives $Dg(y) = Df(g(y))^{-1}$. So
$$Dg = \mathrm{Inv} \circ Df \circ g \quad \text{on } V,$$
where $\mathrm{Inv}(T) = T^{-1}$ on the open set of invertible maps. By Chapter 2, $\mathrm{Inv}$ is differentiable with $D\,\mathrm{Inv}(T)(H) = -T^{-1}HT^{-1}$, and Chapter 4 shows that it is $C^\infty$.

Induction on $j$ shows that $g$ is $C^j$ on $V$ for each $j \le k$. The case $j = 0$ holds: $g$ is continuous. If $g$ is $C^j$ with $j < k$, then $Df$ is $C^{k-1}$, hence $C^j$, and the composition $\mathrm{Inv} \circ Df \circ g$ of $C^j$ maps is $C^j$ by Chapter 4. So $Dg$ is $C^j$, and $g$ is $C^{j+1}$ by the characterization $C^{j+1} \iff$ differentiable with a $C^j$ derivative. For $k = \infty$ the induction gives every $j$. $\square$

::: mathlib
`ContDiffAt.to_localInverse` · `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff`

For `hf : ContDiffAt 𝕂 n f a` with `[RCLike 𝕂]`, `hf' : HasFDerivAt f (f' : E →L[𝕂] F) a` for an equivalence `f'`, and `hn : n ≠ 0`, it gives `ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a)`. The objects are `ContDiffAt.toOpenPartialHomeomorph` and `ContDiffAt.localInverse`, defined through the strict derivative. The proof uses `OpenPartialHomeomorph.contDiffAt_symm` from the library of Chapter 4, which is the induction above. Since `n : WithTop ℕ∞`, the value `n = ω` is allowed and gives the analytic case.

<?decl ContDiffAt.to_localInverse?>
:::

In one variable, the hypothesis reads $f'(a) \ne 0$. Mathlib has `HasStrictDerivAt.localInverse` and `HasStrictDerivAt.to_localInverse`, with the derivative $f'(a)^{-1}$ at $f(a)$, and `isOpenMap_of_hasStrictDerivAt`: a map with a nonzero strict derivative at every point is an open map.

In finite dimension over $\mathbb{R}$, `ApproximatesLinearOn.exists_homeomorph_extension` extends an approximately linear map on $s$ with a small constant to a homeomorphism of the whole space. Measure theory uses it for the change of variables formula.

### Examples

**Example (A triangular map).** Let $f(x, y) = (x + y^2, y)$ on $\mathbb{R}^2$. Then
$$Df(x, y) = \begin{pmatrix} 1 & 2y \\ 0 & 1 \end{pmatrix},$$
with determinant $1$, so the theorem applies at every point. Here the inverse is global and explicit: $u = x + y^2$ and $v = y$ give $g(u, v) = (u - v^2, v)$. Its derivative is
$$Dg(u, v) = \begin{pmatrix} 1 & -2v \\ 0 & 1 \end{pmatrix}.$$
The formula of the theorem predicts $Dg(u, v) = Df(g(u, v))^{-1}$. At $g(u, v)$ the second coordinate is $y = v$, and
$$\begin{pmatrix} 1 & 2v \\ 0 & 1 \end{pmatrix}^{-1} = \begin{pmatrix} 1 & -2v \\ 0 & 1 \end{pmatrix},$$
which agrees.

**Example (Polar coordinates).** Let $P(r, \theta) = (r\cos\theta, r\sin\theta)$ on $(0, \infty) \times \mathbb{R}$. Then
$$DP(r, \theta) = \begin{pmatrix} \cos\theta & -r\sin\theta \\ \sin\theta & r\cos\theta \end{pmatrix}, \qquad \det DP(r, \theta) = r > 0.$$
So $P$ has a smooth local inverse at every point. At $(1, 0)$ the derivative is the identity, and on the half plane $x > 0$ a local inverse is
$$g(x, y) = \Big(\sqrt{x^2 + y^2},\ \arctan\frac{y}{x}\Big).$$
The map $P$ is not injective, because $P(r, \theta + 2\pi) = P(r, \theta)$. So it has no global inverse, although it has a local inverse everywhere.

**Counterexample (Differentiability is not enough).** Let $f(x) = x + 2x^2\sin(1/x)$ for $x \ne 0$ and $f(0) = 0$. Then $f'(0) = \lim_{x \to 0}(1 + 2x\sin(1/x)) = 1 \ne 0$. For $x \ne 0$,
$$f'(x) = 1 + 4x\sin(1/x) - 2\cos(1/x).$$
At $x = 1/(2\pi n)$ this is $-1$, and at $x = 1/((2n+1)\pi)$ it is $3$. So every neighbourhood of $0$ contains points where $f$ decreases and points where it increases. A continuous injective function on an interval is monotone, so $f$ is injective on no neighbourhood of $0$. The derivative exists everywhere but is not continuous at $0$, and $f$ is not strictly differentiable at $0$.

**Counterexample (An invertible derivative is needed).** The map $f(x) = x^3$ is a homeomorphism of $\mathbb{R}$, but $f'(0) = 0$. Its inverse $y \mapsto y^{1/3}$ is not differentiable at $0$. If $g$ were differentiable at $0$, the chain rule applied to $g \circ f = \mathrm{id}$ would give $g'(0) f'(0) = 1$, which is impossible.

### The library around it

The theorem lives in `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`, with the $C^k$ case in `...InverseFunctionTheorem.ContDiff`, one variable in `...Deriv` and the finite-dimensional extension in `...FiniteDimensional`. All the statements are about strict derivatives and open partial homeomorphisms.

Common errors of a learner:

- Giving the derivative as a `E →L[𝕜] F`. The theorems need `f' : E ≃L[𝕜] F` and the hypothesis `HasStrictFDerivAt f (f' : E →L[𝕜] F) a`. To produce `f'` from an invertible matrix or a bijective map, use `ContinuousLinearEquiv.ofBijective` or, in finite dimension, `LinearEquiv.toContinuousLinearEquiv`.
- Using `HasFDerivAt` where `HasStrictFDerivAt` is needed. The counterexample above shows that the weaker hypothesis does not suffice. Get the strict form from `ContDiffAt.hasStrictFDerivAt`.
- Expecting `localInverse` to be the inverse everywhere. It is only correct near `f a`.

### Exercises

1. (A) Let $f(x) = x + e^x$ on $\mathbb{R}$. Compute $(f^{-1})'(1)$. Hint: $f(0) = 1$.
2. (A) Let $f(x, y) = (x^2 - y^2, 2xy)$. Show that $f$ has a local inverse at each point except $(0, 0)$, and compute $Dg(0, 2)$ for the local inverse $g$ at $(1, 1)$. Hint: the answer is $\frac14\begin{pmatrix} 1 & 1 \\ -1 & 1\end{pmatrix}$.
3. (A) Let $f(x, y) = (e^x\cos y, e^x\sin y)$. Show that $f$ has a local inverse at every point and that it is not injective.
4. (B) Let $f : \mathbb{R}^n \to \mathbb{R}^n$ be $C^1$ with $Df(x)$ invertible for every $x$. Show that $f$ is an open map. Give an example where $f(\mathbb{R}^n) \ne \mathbb{R}^n$.
5. (B) Let $\mathcal{A}$ be a Banach algebra over $\mathbb{R}$. Show that $s(x) = x^2$ has a smooth local inverse at $1$, and that this square root satisfies $\sqrt{1 + h} = 1 + \frac12 h + o(\|h\|)$. Hint: $Ds(1)h = 2h$.
6. (C) Let $f : \mathbb{R}^n \to \mathbb{R}^n$ be $C^1$ with $\|Df(x) - I\| \le \frac12$ for every $x$. Show that $f$ is a diffeomorphism of $\mathbb{R}^n$ onto $\mathbb{R}^n$. Hint: Section 1 and the smooth inverse function theorem.

### Notes and history

The proof by a contraction in a Banach space, and the use of the theorem for $C^k$ maps, are in Dieudonné, *Foundations of Modern Analysis* (1960), Chapter X. The formulation with strict differentiability makes the theorem hold at a single point, without any hypothesis on the other points.

### Reference

<?reference?>
