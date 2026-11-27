---
title: Complex differentiability and the Cauchy-Riemann equations
kind: theory
modules:
  - Mathlib.Analysis.Complex.RealDeriv
  - Mathlib.Analysis.Complex.Conformal
explains:
  E3: [differentiableAt_complex_iff_differentiableAt_real, HasDerivAt.real_of_complex, DifferentiableAt.conformalAt]
  E2: [isConformalMap_iff_is_complex_or_conj_linear, HasDerivAt.complexToReal_fderiv, HasDerivAt.comp_ofReal, HasDerivAt.ofReal_comp, DifferentiableAt.real_of_complex, Differentiable.real_of_complex, ContDiff.real_of_complex, Complex.differentiable_re, Complex.differentiable_conj, conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj, IsConformalMap.is_complex_or_conj_linear, isConformalMap_conj, isConformalMap_complex_linear, ContinuousLinearMap.complexOfReal, complexOfReal_hasDerivAt, real_linearMap_map_smul_complex]
  E1: auto
families: []
requires: [V19.C01, V17.C01, V17.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Complex differentiability and the Cauchy-Riemann equations

### Overview

A map $f : \mathbb{C} \to \mathbb{C}$ can be differentiated in two ways. As a map of a normed field to itself, it can have a complex derivative $f'(z)$, the limit of difference quotients. As a map of the real plane $\mathbb{R}^2$ to itself, it can have a Fréchet derivative, a real linear map $\mathbb{R}^2 \to \mathbb{R}^2$. This section shows that a complex derivative is a real derivative that is complex linear. In coordinates the condition is the pair of Cauchy-Riemann equations.

Two consequences follow. A complex derivative at a real point gives a real derivative of the real part. A holomorphic map with nonzero derivative preserves angles and orientation.

The Fréchet derivative and the chain rule come from Volume 17, Chapters 1 and 2. The classification of isometries of $\mathbb{C}$ comes from Chapter 1, Section 1.

### Definitions

**Definition (Complex derivative).** Let $U \subseteq \mathbb{C}$ be open and $f : U \to \mathbb{C}$. The function $f$ is *complex differentiable* at $z \in U$ if the limit
$$f'(z) = \lim_{h \to 0,\ h \in \mathbb{C}} \frac{f(z + h) - f(z)}{h}$$
exists. It is *holomorphic* on $U$ if it is complex differentiable at every point of $U$. A function holomorphic on all of $\mathbb{C}$ is *entire*.

Equivalently, $f(z + h) = f(z) + f'(z) h + o(|h|)$. This is the Fréchet derivative of Volume 17 over the field $\mathbb{C}$: the derivative is the $\mathbb{C}$-linear map $h \mapsto f'(z) h$.

**Definition (Conformal).** A real linear map $L : \mathbb{C} \to \mathbb{C}$ is *conformal* if $L = c\, T$ for a real $c > 0$ and a real linear isometry $T$. A map $f$ is *conformal at* $z$ if it is real differentiable at $z$ and its derivative there is conformal.

A conformal linear map multiplies lengths by $c$ and preserves angles.

::: mathlib
`DifferentiableAt` · `Mathlib.Analysis.Calculus.FDeriv.Defs`

Mathlib has one notion of derivative, `DifferentiableAt 𝕜 f x`, for a field `𝕜`. Complex differentiability is `DifferentiableAt ℂ f z`, and real differentiability of the same map is `DifferentiableAt ℝ f z`;. The derivative as a number is `deriv f z`, and `HasDerivAt f f' z` states that it equals `f'`. There is no separate word for holomorphic: `DifferentiableOn ℂ f U` on an open `U` plays that role, and `Differentiable ℂ f` means entire.

<?decl DifferentiableAt?>
:::

### Theorems and proofs

**Lemma (Complex linear maps).** A real linear map $L : \mathbb{C} \to \mathbb{C}$ is complex linear if and only if $L(i) = i L(1)$. In that case $L(h) = L(1) h$ for all $h$.

*Proof.* If $L$ is complex linear then $L(i) = L(i \cdot 1) = i L(1)$. Conversely, let $L(i) = iL(1)$ and $h = x + iy$. Real linearity gives $L(h) = x L(1) + y L(i) = (x + iy) L(1) = L(1) h$. The map $h \mapsto L(1) h$ is complex linear. $\square$

**Theorem (Complex and real derivatives).** Let $f : \mathbb{C} \to \mathbb{C}$. Then $f$ is complex differentiable at $z$ if and only if $f$ is real differentiable at $z$ and its real derivative $L = Df(z)$ satisfies $L(i) = i L(1)$. In that case $f'(z) = L(1)$.

*Proof.* Let $f$ be complex differentiable at $z$, and put $L(h) = f'(z) h$. Then $L$ is real linear and
$$|f(z + h) - f(z) - L(h)| = o(|h|),$$
which is the definition of the real derivative. Also $L(i) = i f'(z) = iL(1)$. Conversely, let $f$ be real differentiable at $z$ with $L(i) = iL(1)$. By the lemma, $L(h) = L(1) h$. Then
$$\Big|\frac{f(z + h) - f(z)}{h} - L(1)\Big| = \frac{|f(z + h) - f(z) - L(h)|}{|h|} \to 0,$$
so $f'(z) = L(1)$. $\square$

**Corollary (Cauchy-Riemann equations).** Write $f = u + iv$ with real $u, v$ and $z = x + iy$. Then $f$ is complex differentiable at $z$ if and only if it is real differentiable at $z$ and
$$\frac{\partial u}{\partial x} = \frac{\partial v}{\partial y}, \qquad \frac{\partial u}{\partial y} = -\frac{\partial v}{\partial x}.$$
In that case $f'(z) = u_x + i v_x = v_y - i u_y$.

*Proof.* The real derivative maps $1$ to the partial derivative in $x$ and $i$ to the partial derivative in $y$: $L(1) = u_x + iv_x$ and $L(i) = u_y + i v_y$. The condition $L(i) = iL(1)$ reads $u_y + iv_y = -v_x + i u_x$. Compare real and imaginary parts. $\square$

::: mathlib
`differentiableAt_complex_iff_differentiableAt_real` · `Mathlib.Analysis.Complex.Conformal`

The statement, for `f : ℂ → E` with `E` a complex normed space, is `DifferentiableAt ℂ f x ↔ DifferentiableAt ℝ f x ∧ fderiv ℝ f x I = I • fderiv ℝ f x 1`. This is the coordinate-free form of the theorem. The lemma `real_linearMap_map_smul_complex` is the lemma above, and `ContinuousLinearMap.complexOfReal` turns such an `ℓ : ℂ →L[ℝ] E` into a `ℂ →L[ℂ] E`. One direction alone is `DifferentiableAt.real_of_complex`.

<?decl differentiableAt_complex_iff_differentiableAt_real?>
:::

**Theorem (Restriction to the real line).** Let $e : \mathbb{C} \to \mathbb{C}$ be complex differentiable at a real point $x$, with derivative $e'$. Then the real function $t \mapsto \operatorname{Re} e(t)$ is differentiable at $x$, with derivative $\operatorname{Re} e'$.

*Proof.* The inclusion $\iota : \mathbb{R} \to \mathbb{C}$ is real linear, so its derivative is $\iota$ and $\iota(1) = 1$. By the chain rule (Volume 17, Chapter 2), $t \mapsto e(\iota(t))$ is differentiable at $x$ as a map $\mathbb{R} \to \mathbb{C}$, with derivative $e' \cdot 1 = e'$. The real part $\operatorname{Re} : \mathbb{C} \to \mathbb{R}$ is real linear and continuous, so the chain rule again gives the derivative $\operatorname{Re} e'$ of $t \mapsto \operatorname{Re} e(t)$. $\square$

::: mathlib
`HasDerivAt.real_of_complex` · `Mathlib.Analysis.Complex.RealDeriv`

The statement is `HasDerivAt e e' ↑z → HasDerivAt (fun x : ℝ ↦ (e ↑x).re) e'.re z` for `e : ℂ → ℂ`. Mathlib gets the derivatives of `Real.exp`, `Real.sin` and `Real.cos` this way, since they are real parts of complex functions. The first step of the proof alone is `HasDerivAt.comp_ofReal`. The smooth version is `ContDiff.real_of_complex`. In the other direction, `HasDerivAt.complexToReal_fderiv` says that a complex derivative `f'` gives the real Fréchet derivative `f' • 1`.

<?decl HasDerivAt.real_of_complex?>
:::

**Theorem (Conformal linear maps).** A real linear map $L : \mathbb{C} \to \mathbb{C}$ is conformal if and only if $L \ne 0$ and either $L$ is complex linear or $L$ composed with conjugation is complex linear. That is, $L(h) = ah$ or $L(h) = a\bar h$ with $a \ne 0$.

*Proof.* Let $L = cT$ with $c > 0$ and $T$ an isometry. By Chapter 1, Section 1, $T(h) = bh$ or $T(h) = b \bar h$ with $|b| = 1$. Put $a = cb$; then $a \ne 0$. Conversely, let $L(h) = ah$ with $a \ne 0$. Put $c = |a|$ and $b = a/|a|$. Then $|b| = 1$, so $h \mapsto bh$ is an isometry and $L = cT$. The case $L(h) = a\bar h$ is the same, since conjugation is an isometry. $\square$

**Corollary (Holomorphic maps are conformal).** If $f$ is complex differentiable at $z$ and $f'(z) \ne 0$, then $f$ is conformal at $z$. The derivative preserves orientation: its determinant is $|f'(z)|^2 > 0$.

*Proof.* The real derivative is $h \mapsto f'(z) h$, which is conformal by the theorem. For the determinant, write $f'(z) = p + iq$. Multiplication by $p + iq$ maps $1$ to $p + iq$ and $i$ to $-q + ip$, so its matrix is $\begin{pmatrix} p & -q \\ q & p \end{pmatrix}$, of determinant $p^2 + q^2$. $\square$

::: mathlib
`DifferentiableAt.conformalAt` · `Mathlib.Analysis.Complex.Conformal`

The statement is `DifferentiableAt ℂ f z → deriv f z ≠ 0 → ConformalAt f z`, for `f : ℂ → E`. The predicate `ConformalAt` comes from `Mathlib.Analysis.Calculus.Conformal.NormedSpace`, and the linear notion is `IsConformalMap`. The converse is `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj`. For linear maps, the theorem above is `isConformalMap_iff_is_complex_or_conj_linear`, and `isConformalMap_conj` covers conjugation.

<?decl DifferentiableAt.conformalAt?>
<?decl ConformalAt?>
:::

### Examples

**Example.** Polynomials are entire, with the usual derivative. The exponential is entire with $\exp' = \exp$. In coordinates, $e^{x+iy} = e^x\cos y + ie^x \sin y$, so $u_x = e^x \cos y = v_y$ and $u_y = -e^x\sin y = -v_x$.

**Example.** Conjugation $f(z) = \bar z$ has $u = x$ and $v = -y$. Then $u_x = 1$ and $v_y = -1$, so $f$ is complex differentiable at no point. It is real linear, hence real differentiable everywhere, and it is conformal: it reverses orientation.

**Example.** Let $f(z) = |z|^2 = x^2 + y^2$, so $u = x^2 + y^2$ and $v = 0$. The equations read $2x = 0$ and $2y = 0$. So $f$ is complex differentiable at $0$ only, with $f'(0) = 0$, and it is holomorphic on no open set.

**Example.** The map $z^2$ doubles angles at $0$, where its derivative vanishes. So the corollary needs $f'(z) \ne 0$.

::: mathlib
`Complex.hasDerivAt_exp` · `Mathlib.Analysis.SpecialFunctions.ExpDeriv`

The derivatives of the elementary functions live in the special functions of Volume 15: `Complex.hasDerivAt_exp x : HasDerivAt exp (exp x) x`.

<?decl Complex.hasDerivAt_exp?>
:::

### The library around it

Common errors of a learner:

- Confusing `DifferentiableAt ℝ f z` and `DifferentiableAt ℂ f z` for `f : ℂ → ℂ`. A goal stated over `ℝ` follows from one over `ℂ` by `DifferentiableAt.real_of_complex`, but not conversely.
- Looking for a predicate `Holomorphic`. Use `DifferentiableOn ℂ f U` with `IsOpen U`, or `AnalyticOnNhd ℂ f U`. Section 3 shows that they agree on open sets.
- Expecting `Complex.re` to be complex differentiable. It is only real differentiable (`Complex.differentiable_re`), and so is conjugation (`Complex.differentiable_conj`).

### Exercises

1. (A) Use the Cauchy-Riemann equations to show that $f(x + iy) = x^3 - 3xy^2 + i(3x^2 y - y^3)$ is entire. Identify $f$. Hint: expand $(x + iy)^3$.
2. (A) Find the points where $f(z) = \bar z^2$ is complex differentiable.
3. (B) Let $f = u + iv$ be holomorphic on an open connected $U$ and real valued. Show that $f$ is constant. Hint: $v = 0$ gives $u_x = u_y = 0$; use the mean value inequality of Volume 17, Chapter 3.
4. (B) Let $f$ be holomorphic on $U$ with $|f|$ constant. Show that $f$ is constant on each connected component of $U$. Hint: if $|f|^2 = u^2 + v^2 = c \ne 0$, differentiate and use the equations to get a linear system for $u_x, v_x$ of determinant $u^2 + v^2$.
5. (B) Show that if $f$ is holomorphic, $f = u + iv$, and $u, v$ are $C^2$, then $u_{xx} + u_{yy} = 0$. Hint: differentiate the equations. Chapter 5 studies such harmonic functions.
6. (C) Show that a real linear $L : \mathbb{C} \to \mathbb{C}$ with $L \ne 0$ that preserves the angle between any two nonzero vectors is conformal. Hint: $L$ maps the orthonormal pair $1, i$ to an orthogonal pair; then use $1 + i$ to show that the two images have the same length.

### Notes and history

The equations are named after Cauchy and Riemann. Riemann made them the starting point of the theory in his doctoral thesis of 1851, while Cauchy started from integrals.

### Reference

<?reference?>
