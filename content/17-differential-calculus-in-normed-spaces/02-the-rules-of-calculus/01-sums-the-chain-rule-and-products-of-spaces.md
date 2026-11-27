---
title: Sums, the chain rule and maps into products
kind: theory
modules:
  - Mathlib.Analysis.Calculus.FDeriv.Add
  - Mathlib.Analysis.Calculus.FDeriv.Comp
  - Mathlib.Analysis.Calculus.FDeriv.Prod
  - Mathlib.Analysis.Calculus.FDeriv.Equiv
explains:
  E3: [HasFDerivAt.comp, HasFDerivAt.add, HasFDerivAt.prodMk]
  E2: [HasFDerivAt.const_smul, HasFDerivAt.sub, HasFDerivAt.sum, fderiv_add, fderiv_comp, DifferentiableAt.comp, hasFDerivAt_fst, hasFDerivAt_prodMk_left, hasFDerivAt_pi, ContinuousLinearEquiv.comp_hasFDerivAt_iff]
  E1: auto
families: []
requires: [V17.C01, V07, V15.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sums, the chain rule and maps into products

### Overview

This section proves the rules that make the computation of derivatives mechanical: the derivative of a sum is the sum of the derivatives, the derivative of a composite is the composite of the derivatives, and a map into a product of spaces is differentiable if and only if each component is. The main theorem is the chain rule $D(g \circ f)(x) = Dg(f(x)) \circ Df(x)$, which has the same form in every dimension. The section then explains partial derivatives on a product $E_1 \times E_2$ as restrictions of the derivative, and shows that a continuous linear equivalence does not change differentiability.

Throughout, $E$, $F$, $G$ are normed spaces over a nontrivially normed field $\mathbb{K}$, for example $\mathbb{R}$ or $\mathbb{C}$, and $L(E, F)$ is the space of continuous linear maps with the operator norm.

### Definitions

**Definition (Norm on a product).** The product $F \times G$ has the norm $\|(u, w)\| = \max(\|u\|, \|w\|)$. A finite product $\prod_{i \in \iota} F_i$ has the norm $\|u\| = \max_i \|u_i\|$.

The projections $\pi_1(u, w) = u$, $\pi_2(u, w) = w$ and the inclusions $\iota_1(u) = (u, 0)$, $\iota_2(w) = (0, w)$ are continuous linear maps of norm at most $1$. All norms on a finite-dimensional space are equivalent (Volume 16), and $r(h) = o(\|h\|)$ does not change when a norm is replaced by an equivalent one. So differentiability in $\mathbb{R}^n$ does not depend on the norm.

**Definition (Pairing of maps).** For $f_1 : E \to F$ and $f_2 : E \to G$, the map $(f_1, f_2) : E \to F \times G$ is $x \mapsto (f_1(x), f_2(x))$. For $L_1 \in L(E, F)$ and $L_2 \in L(E, G)$, the map $(L_1, L_2) \in L(E, F \times G)$ is $h \mapsto (L_1 h, L_2 h)$.

::: mathlib
`HasFDerivAt.prodMk` · `Mathlib.Analysis.Calculus.FDeriv.Prod`

The pairing of maps is the anonymous constructor `fun x => (f₁ x, f₂ x)`, and the pairing of continuous linear maps is `ContinuousLinearMap.prod f₁' f₂'`, written `f₁'.prod f₂'`. The lemma states `HasFDerivAt f₁ f₁' x → HasFDerivAt f₂ f₂' x → HasFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x`. The projections are `ContinuousLinearMap.fst` and `ContinuousLinearMap.snd`,.

<?decl HasFDerivAt.prodMk?>
<?decl ContinuousLinearMap.prod?>
:::

### Theorems and proofs

In each proof, $r_f(h) = f(x + h) - f(x) - Df(x)h$ denotes the remainder of $f$ at $x$.

**Theorem (Sums and scalar multiples).** Let $f, g : E \to F$ be differentiable at $x$ and $c \in \mathbb{K}$. Then $f + g$ and $cf$ are differentiable at $x$, with $D(f + g)(x) = Df(x) + Dg(x)$ and $D(cf)(x) = c\,Df(x)$.

*Proof.* The remainders satisfy $r_{f+g} = r_f + r_g$ and $r_{cf} = c\,r_f$, for the candidates $Df(x) + Dg(x)$ and $c\,Df(x)$. If $\|r_f(h)\| \le \varepsilon\|h\|$ and $\|r_g(h)\| \le \varepsilon\|h\|$ for $\|h\| < \delta$, then $\|r_{f+g}(h)\| \le 2\varepsilon\|h\|$ and $\|r_{cf}(h)\| \le |c|\varepsilon\|h\|$ there. $\square$

By induction the same holds for a finite sum.

::: mathlib
`HasFDerivAt.add` · `Mathlib.Analysis.Calculus.FDeriv.Add`

`HasFDerivAt f f' x → HasFDerivAt g g' x → HasFDerivAt (fun y => f y + g y) (f' + g') x`. The companions are `HasFDerivAt.sub`, `HasFDerivAt.const_smul` and `HasFDerivAt.sum` for a `Finset`. For the function `fderiv`, the rule is `fderiv_add`, which needs both maps to be differentiable at `x`: otherwise the junk value $0$ makes the equation false.

<?decl HasFDerivAt.add?>
<?decl HasFDerivAt.sub?>
<?decl HasFDerivAt.const_smul?>
<?decl HasFDerivAt.sum?>
<?decl fderiv_add?>
:::

**Theorem (Chain rule).** Let $f : E \to F$ be differentiable at $x$ and $g : F \to G$ be differentiable at $f(x)$. Then $g \circ f$ is differentiable at $x$, and
$$D(g \circ f)(x) = Dg(f(x)) \circ Df(x).$$

*Proof.* Put $y = f(x)$, $L = Df(x)$, $M = Dg(y)$, and let $r = r_f$ at $x$ and $s = r_g$ at $y$. For $h \in E$ put $k(h) = f(x + h) - f(x) = Lh + r(h)$. Then
$$g(f(x + h)) - g(f(x)) - MLh = g(y + k(h)) - g(y) - Mk(h) + M\big(k(h) - Lh\big) = s(k(h)) + M r(h).$$
So it suffices to show that both terms on the right are $o(\|h\|)$.

The second term: $\|Mr(h)\| \le \|M\|\,\|r(h)\|$, and $r(h) = o(\|h\|)$.

The first term. Since $r(h) = o(\|h\|)$, there is $\delta_1 > 0$ with $\|r(h)\| \le \|h\|$ for $\|h\| < \delta_1$. For these $h$,
$$\|k(h)\| \le \|L\|\,\|h\| + \|h\| = (\|L\| + 1)\|h\|.$$
Let $\varepsilon > 0$. Since $s(k) = o(\|k\|)$, there is $\eta > 0$ with $\|s(k)\| \le \varepsilon\|k\|$ for $\|k\| < \eta$. Put $\delta = \min\big(\delta_1, \eta/(\|L\| + 1)\big)$. For $\|h\| < \delta$, $\|k(h)\| < \eta$, so
$$\|s(k(h))\| \le \varepsilon\|k(h)\| \le \varepsilon(\|L\| + 1)\|h\|.$$
Since $\varepsilon$ is arbitrary, $s(k(h)) = o(\|h\|)$. $\square$

The bound $\|k(h)\| \le C\|h\|$ is the key step. It replaces the division by $k(h)$ in the usual false proof of the one-variable chain rule, which fails when $k(h) = 0$ for $h$ arbitrarily small.

::: mathlib
`HasFDerivAt.comp` · `Mathlib.Analysis.Calculus.FDeriv.Comp`

`HasFDerivAt.comp x (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp f') x`. The point `x` is an explicit argument, because Lean cannot find it from the hypothesis on `g`, which mentions only `f x`. The function forms are `fderiv_comp`, with the two hypotheses of differentiability, and `DifferentiableAt.comp`. For a curve, `HasFDerivAt.comp_hasDerivAt` combines a Fréchet derivative with the derivative of Volume 15.

<?decl HasFDerivAt.comp?>
<?decl fderiv_comp?>
<?decl DifferentiableAt.comp?>
<?decl HasFDerivAt.comp_hasDerivAt?>
:::

**Theorem (Maps into a product).** The map $f = (f_1, f_2) : E \to F \times G$ is differentiable at $x$ if and only if $f_1$ and $f_2$ are. Then $Df(x) = (Df_1(x), Df_2(x))$. The same holds for a finite product $\prod_i F_i$, with $Df(x)h = (Df_i(x)h)_i$.

*Proof.* Assume $f_1$ and $f_2$ are differentiable at $x$. The remainder of $f$ for the candidate $(Df_1(x), Df_2(x))$ is $(r_{f_1}(h), r_{f_2}(h))$, and its norm is $\max(\|r_{f_1}(h)\|, \|r_{f_2}(h)\|)$. If both are at most $\varepsilon\|h\|$ for $\|h\| < \delta$, so is the max. Conversely, assume $f$ is differentiable at $x$. Then $f_1 = \pi_1 \circ f$, and $\pi_1$ is continuous linear, so it is its own derivative at each point (Chapter 1). By the chain rule, $f_1$ is differentiable with $Df_1(x) = \pi_1 \circ Df(x)$, and the same for $f_2$. For a finite product the proof is the same, with the max over $i$ and the projections $\pi_i$. $\square$

::: mathlib
`hasFDerivAt_pi` · `Mathlib.Analysis.Calculus.FDeriv.Prod`

For a family `φ i : E → F' i` over a `Fintype ι`, `HasFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔ ∀ i, HasFDerivAt (φ i) (φ' i) x`. The projections give `hasFDerivAt_fst`, `hasFDerivAt_snd` and `hasFDerivAt_apply`. The inclusion `e ↦ (e, f₀)` has the derivative `ContinuousLinearMap.inl 𝕜 E F` by `hasFDerivAt_prodMk_left`.

<?decl hasFDerivAt_pi?>
<?decl hasFDerivAt_fst?>
<?decl hasFDerivAt_prodMk_left?>
:::

**Theorem (Partial derivatives on a product).** Let $f : E_1 \times E_2 \to F$ be differentiable at $x = (x_1, x_2)$. Define the *partial derivatives* $D_1 f(x) = Df(x) \circ \iota_1 \in L(E_1, F)$ and $D_2 f(x) = Df(x) \circ \iota_2 \in L(E_2, F)$. Then $D_1 f(x)$ is the derivative of $u \mapsto f(u, x_2)$ at $x_1$, $D_2 f(x)$ is the derivative of $w \mapsto f(x_1, w)$ at $x_2$, and
$$Df(x)(h_1, h_2) = D_1 f(x)h_1 + D_2 f(x)h_2.$$

*Proof.* The map $j(u) = (u, x_2)$ is $\iota_1$ plus the constant $(0, x_2)$, so $Dj(x_1) = \iota_1$. By the chain rule, $u \mapsto f(j(u))$ has the derivative $Df(x) \circ \iota_1$ at $x_1$. The second case is the same with $w \mapsto (x_1, w)$. Finally $(h_1, h_2) = \iota_1 h_1 + \iota_2 h_2$, and $Df(x)$ is linear. $\square$

For $E_1 = E_2 = \mathbb{R}$ these are the partial derivatives of Section 2 of Chapter 1. The converse is false: the counterexample $x^2y/(x^4 + y^2)$ of that section has both partial derivatives at $0$. Chapter 6 uses $D_2 f$ in the implicit function theorem.

**Theorem (Continuous linear equivalences).** Let $e : F \to G$ be a continuous linear equivalence, that is, a linear bijection with $e$ and $e^{-1}$ continuous. Then $f : E \to F$ is differentiable at $x$ with derivative $L$ if and only if $e \circ f$ is differentiable at $x$ with derivative $e \circ L$.

*Proof.* The map $e$ is its own derivative, so the chain rule gives one direction. For the other, apply the chain rule to $e^{-1} \circ (e \circ f) = f$, with $e^{-1} \circ e \circ L = L$. $\square$

::: mathlib
`ContinuousLinearEquiv.comp_hasFDerivAt_iff` · `Mathlib.Analysis.Calculus.FDeriv.Equiv`

`HasFDerivAt (iso ∘ f) ((iso : F →L[𝕜] G).comp f') x ↔ HasFDerivAt f f' x`. The coercion `(iso : F →L[𝕜] G)` forgets the inverse.

<?decl ContinuousLinearEquiv.comp_hasFDerivAt_iff?>
:::

### Examples

**Example (A function along a curve).** Let $f(x, y) = x^2 y$ and $\gamma(t) = (\cos t, \sin t)$. By Section 2 of Chapter 1, $Df(x, y)(h, k) = 2xy\,h + x^2 k$, and $\gamma'(t) = (-\sin t, \cos t)$. The chain rule gives
$$(f \circ \gamma)'(t) = Df(\gamma(t))\gamma'(t) = -2\cos t\sin^2 t + \cos^3 t.$$
A direct computation agrees: $f(\gamma(t)) = \cos^2 t\sin t$, with derivative $-2\cos t\sin t \cdot \sin t + \cos^2 t\cos t$. At $t = \pi/4$ the value is $-2(\frac{\sqrt2}{2})^3 + (\frac{\sqrt2}{2})^3 = -\frac{\sqrt2}{4}$.

**Example (A norm through a linear map).** Let $E$ be a real inner product space, $A \in L(E, E)$ and $q(x) = \|Ax\|^2$. Chapter 1 gives $D(\|\cdot\|^2)(y)k = 2\langle y, k\rangle$, and $DA(x) = A$. So
$$Dq(x)h = 2\langle Ax, Ah\rangle = 2\langle A^*Ax, h\rangle,$$
and in $\mathbb{R}^n$ the gradient of $q$ is $2A^{\mathsf T}Ax$.



**Counterexample (Product of derivatives in the wrong order).** Let $f(x) = Ax$ and $g(y) = By$ on $\mathbb{R}^2$, with $A = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ and $B = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$. Then $D(g \circ f) = BA = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$, while $AB = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. The chain rule composes in the order of the maps: the derivative of the outer map stands on the left.

### The library around it

Each rule exists in many forms: for `HasFDerivAt`, `HasFDerivWithinAt`, `HasStrictFDerivAt`, `HasFDerivAtFilter`, `DifferentiableAt`, `DifferentiableOn`, `Differentiable` and `fderiv`. In a proof, establish `HasFDerivAt f L x` with an explicit `L` by the rules, then read off `fderiv 𝕜 f x = L` with `HasFDerivAt.fderiv`. The tactic `fun_prop` proves goals of the form `DifferentiableAt 𝕜 f x` by these rules.

Common errors of a learner:

- Writing the chain rule as `f' ∘L g'`. The derivative of the outer map comes first: `g' ∘L f'`.
- Forgetting the explicit point in `HasFDerivAt.comp x hg hf`, or giving `hg` at `x` instead of at `f x`.
- Using `fderiv_add` without the hypotheses of differentiability.
- Expecting the Euclidean norm on `Fin n → ℝ`. Its norm is the max norm, and `EuclideanSpace ℝ (Fin n)` carries the Euclidean one.

### Exercises

1. (A) Let $f(x, y) = (xy, x + y)$ and $g(u, v) = u^2 + v$. Compute $D(g \circ f)(1, 2)$ in two ways: by the chain rule and from the formula of $g \circ f$.
2. (A) Let $\gamma : \mathbb{R} \to E$ be differentiable and $L \in L(E, F)$. Show that $(L \circ \gamma)'(t) = L\gamma'(t)$.
3. (B) Let $E$ be a real inner product space and $\gamma : \mathbb{R} \to E$ differentiable with $\|\gamma(t)\| = 1$ for all $t$. Show that $\langle \gamma(t), \gamma'(t)\rangle = 0$.
4. (B) Let $f : \mathbb{R}^2 \to \mathbb{R}$ be differentiable and $F(r, \theta) = f(r\cos\theta, r\sin\theta)$. Express $\partial_r F$ and $\partial_\theta F$ through $\partial_1 f$ and $\partial_2 f$, and show that $(\partial_r F)^2 + r^{-2}(\partial_\theta F)^2 = \|\nabla f\|^2$ at the corresponding points for $r > 0$.
5. (B) Let $f : \mathbb{R}^n \to \mathbb{R}$ be differentiable with $f(tx) = t^k f(x)$ for all $t > 0$ and $x$. Prove Euler's identity $Df(x)x = k f(x)$. Hint: differentiate $t \mapsto f(tx)$ at $t = 1$.
6. (C) Let $f : E \to F$ and $g : F \to E$ with $g \circ f = \mathrm{id}_E$ near $x$ and $f \circ g = \mathrm{id}_F$ near $f(x)$. Assume $f$ is differentiable at $x$ and $g$ at $f(x)$. Show that $Df(x)$ is a continuous linear equivalence with inverse $Dg(f(x))$. Deduce that there is no differentiable bijection $\mathbb{R}^2 \to \mathbb{R}$ with a differentiable inverse.

### Notes and history

The chain rule for functions of one variable goes back to Leibniz. The form $D(g \circ f)(x) = Dg(f(x)) \circ Df(x)$, as a composition of linear maps, is the point of view of Fréchet's derivative, and it made the rule the same in every dimension. In coordinates it is the product of the Jacobian matrices.

### Reference

<?reference?>
