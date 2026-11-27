---
title: The Fréchet derivative
kind: theory
modules:
  - Mathlib.Analysis.Calculus.FDeriv.Defs
  - Mathlib.Analysis.Calculus.FDeriv.Basic
  - Mathlib.Analysis.Calculus.FDeriv.Const
  - Mathlib.Analysis.Calculus.FDeriv.Linear
explains:
  E3: [HasFDerivAt, fderiv, HasFDerivAt.unique, HasFDerivAt.continuousAt]
  E2: [DifferentiableAt, hasFDerivAt_iff_isLittleO_nhds_zero, HasFDerivAt.fderiv, fderiv_zero_of_not_differentiableAt, ContinuousLinearMap.hasFDerivAt, hasFDerivAt_const, HasFDerivAtFilter]
  E1: auto
families: []
requires: [V07, V13, V15.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Fréchet derivative

### Overview

In one variable the derivative $f'(a)$ is a number, a slope. For a map $f : E \to F$ between normed spaces a slope makes no sense, because $E$ has many directions. The right object is the linear approximation itself: a continuous linear map $Df(x) : E \to F$ with $f(x + h) = f(x) + Df(x)h + o(\|h\|)$. This section defines this derivative, proves that it is unique and that a differentiable map is continuous, and computes it in five examples. The one-variable derivative of Volume 15, Chapter 3 is the special case $E = \mathbb{K}$.

Throughout, $E$ and $F$ are normed spaces over $\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. Volume 16 defines the space $L(E, F)$ of continuous linear maps with the operator norm $\|A\| = \sup_{h \neq 0} \|Ah\|/\|h\|$, so that $\|Ah\| \le \|A\|\,\|h\|$.

### Definitions

As in Volume 15, Chapter 7, $r(h) = o(\|h\|)$ as $h \to 0$ means: for each $\varepsilon > 0$ there is $\delta > 0$ with $\|r(h)\| \le \varepsilon \|h\|$ for $\|h\| < \delta$.

**Definition (Fréchet derivative).** Let $U \subseteq E$ be a neighbourhood of $x$ and $f : U \to F$. A continuous linear map $L \in L(E, F)$ is a *derivative of $f$ at $x$* if
$$f(x + h) = f(x) + Lh + r(h), \qquad r(h) = o(\|h\|) \text{ as } h \to 0.$$
Then $f$ is *differentiable at $x$*.

So $\|f(x + h) - f(x) - Lh\|/\|h\| \to 0$ as $h \to 0$. The next theorem shows that $L$ is unique. It is the *Fréchet derivative* $Df(x)$, also written $f'(x)$.

**Remark (Why the derivative is continuous).** Let $L$ be linear, not assumed continuous, with $f(x + h) - f(x) - Lh = o(\|h\|)$, and let $f$ be continuous at $x$. Then $Lh = f(x + h) - f(x) - r(h) \to 0$ as $h \to 0$, so $L$ is continuous at $0$, and a linear map continuous at $0$ is continuous. Without the condition $L \in L(E, F)$, a discontinuous linear map would be its own derivative, and a differentiable map need not be continuous.

::: mathlib
`HasFDerivAt` · `Mathlib.Analysis.Calculus.FDeriv.Defs`

`HasFDerivAt f f' x` says that `f' : E →L[𝕜] F` is a derivative of `f : E → F` at `x`. Mathlib defines it through the structure `HasFDerivAtFilter f f' L` for a filter `L` on `E × E`: the condition is `f p.1 - f p.2 - f' (p.1 - p.2) = o(p.1 - p.2)` along `L`. For `HasFDerivAt` the filter is `𝓝 x ×ˢ pure x`, so the second point is fixed at `x`; other filters give the derivative within a set (Section 2) and the strict derivative (Chapter 3). The little-o is `IsLittleOTVS`, which needs no norm. For normed spaces, `hasFDerivAt_iff_isLittleO_nhds_zero` gives the textbook form `(fun h => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h`.

<?decl HasFDerivAt?>
<?decl hasFDerivAt_iff_isLittleO_nhds_zero?>
:::

**Definition (The derivative function in Mathlib).** For $f : E \to F$ and $x \in E$, $\operatorname{fderiv} f\,x \in L(E, F)$ is the derivative of $f$ at $x$ if $f$ is differentiable at $x$, and $0$ otherwise.

An equation `fderiv 𝕜 f x = A` says nothing about $f$ unless $f$ is differentiable at $x$.

::: mathlib
`fderiv` · `Mathlib.Analysis.Calculus.FDeriv.Defs`

`fderiv 𝕜 f x : E →L[𝕜] F`. The field `𝕜` is an explicit argument, because a complex space is also a real space and the two derivatives differ: $z \mapsto \bar z$ on $\mathbb{C}$ has a real derivative and no complex one. The bridges are `HasFDerivAt.fderiv : HasFDerivAt f f' x → fderiv 𝕜 f x = f'` and `DifferentiableAt.hasFDerivAt`, and the junk value is `fderiv_zero_of_not_differentiableAt`.

<?decl fderiv?>
<?decl fderiv_zero_of_not_differentiableAt?>
:::

### Theorems and proofs

**Theorem (Uniqueness of the derivative).** Let $x$ be an interior point of the domain of $f$. If $L_1$ and $L_2$ are derivatives of $f$ at $x$, then $L_1 = L_2$.

*Proof.* Let $A = L_1 - L_2$. Subtracting the two expansions gives $Ah = r_2(h) - r_1(h)$, and the right side is $o(\|h\|)$. Fix $v \in E$ with $v \neq 0$, and let $\varepsilon > 0$. There is $\delta > 0$ with $\|Ah\| \le \varepsilon\|h\|$ for $\|h\| < \delta$. Choose $t \in \mathbb{K}$ with $0 < |t| < \delta/\|v\|$ and put $h = tv$. Then $|t|\,\|Av\| = \|A(tv)\| \le \varepsilon |t|\,\|v\|$, and division by $|t| > 0$ gives $\|Av\| \le \varepsilon\|v\|$. This holds for each $\varepsilon > 0$, so $Av = 0$. Since $v$ is arbitrary, $A = 0$. $\square$



::: mathlib
`HasFDerivAt.unique` · `Mathlib.Analysis.Calculus.FDeriv.Basic`

`HasFDerivAt f f' x → HasFDerivAt f f₁' x → f' = f₁'`. The proof applies `UniqueDiffWithinAt.eq` to the whole space.

<?decl HasFDerivAt.unique?>
:::

**Theorem (Differentiable implies continuous).** If $f$ is differentiable at $x$, then there are $\delta > 0$ and $C \ge 0$ with $\|f(x + h) - f(x)\| \le C\|h\|$ for $\|h\| < \delta$. In particular $f$ is continuous at $x$.

*Proof.* Let $L = Df(x)$. With $\varepsilon = 1$ in the definition of $o(\|h\|)$ there is $\delta > 0$ with $\|r(h)\| \le \|h\|$ for $\|h\| < \delta$. Then
$$\|f(x + h) - f(x)\| = \|Lh + r(h)\| \le \|L\|\,\|h\| + \|h\| = (\|L\| + 1)\|h\|.$$
So $C = \|L\| + 1$ works. As $h \to 0$ the right side tends to $0$, so $f(x + h) \to f(x)$. $\square$

::: mathlib
`HasFDerivAt.continuousAt` · `Mathlib.Analysis.Calculus.FDeriv.Basic`

`HasFDerivAt f f' x → ContinuousAt f x`.

<?decl HasFDerivAt.continuousAt?>
:::

**Theorem (The one-variable case).** Let $f : \mathbb{K} \to F$. Then $f$ has the derivative $f'(a) \in F$ at $a$ in the sense of Volume 15 if and only if $f$ is Fréchet differentiable at $a$, and then $Df(a)h = h\,f'(a)$ for $h \in \mathbb{K}$.

*Proof.* A linear map $L : \mathbb{K} \to F$ is determined by $v = L(1)$, because $L(h) = hL(1) = hv$, and it is continuous with $\|L\| = \|v\|$. The condition $f(a + h) - f(a) - hv = o(|h|)$ means, after division by $|h|$, that $\big\|\frac{f(a + h) - f(a)}{h} - v\big\| \to 0$. This is the statement that the slope tends to $v$. So $L$ is a Fréchet derivative if and only if $v$ is the derivative of Volume 15. $\square$

::: mathlib
`hasDerivAt_iff_hasFDerivAt` · `Mathlib.Analysis.Calculus.Deriv.Basic`

`HasDerivAt f f' x ↔ HasFDerivAt f (smulRight 1 f') x`. The map `smulRight 1 f'` is $h \mapsto h \cdot f'$.

<?decl hasDerivAt_iff_hasFDerivAt?>
:::

### Examples

**Example (Constants and continuous linear maps).** If $f(x) = c$, then $f(x + h) - f(x) = 0$, so $Df(x) = 0$ with remainder $0$. If $f = A \in L(E, F)$, then $f(x + h) = f(x) + Ah$ exactly, so $DA(x) = A$ at every point $x$.

::: mathlib
`ContinuousLinearMap.hasFDerivAt` · `Mathlib.Analysis.Calculus.FDeriv.Linear`

For `f : E →L[𝕜] F`, `HasFDerivAt f f x`; the `fderiv` form is `ContinuousLinearMap.fderiv`. For constants the lemma is `hasFDerivAt_const c x : HasFDerivAt (fun _ => c) 0 x`, in `Mathlib.Analysis.Calculus.FDeriv.Const`.

<?decl ContinuousLinearMap.hasFDerivAt?>
<?decl hasFDerivAt_const?>
:::

**Example (A quadratic form).** Let $A$ be a real $n \times n$ matrix and $q(x) = \langle Ax, x\rangle$ on $\mathbb{R}^n$ with the Euclidean inner product. Bilinearity gives
$$q(x + h) = \langle Ax, x\rangle + \langle Ax, h\rangle + \langle Ah, x\rangle + \langle Ah, h\rangle.$$
The middle terms are linear in $h$, and $\langle Ah, x\rangle = \langle h, A^{\mathsf T}x\rangle$. The last term satisfies $|\langle Ah, h\rangle| \le \|A\|\,\|h\|^2$ by Cauchy-Schwarz, so it is $o(\|h\|)$. So
$$Dq(x)h = \langle (A + A^{\mathsf T})x, h\rangle.$$
For a symmetric $A$ this is $2\langle Ax, h\rangle$, the analogue of $(ax^2)' = 2ax$. For $A = \begin{pmatrix} 1 & 2 \\ 0 & 3\end{pmatrix}$, $q(x, y) = x^2 + 2xy + 3y^2$ and $(A + A^{\mathsf T})(x, y) = (2x + 2y, 2x + 6y)$, the vector of the partial derivatives of $q$.

**Example (The square of a matrix).** Let $E = M_n(\mathbb{R})$ with the operator norm, so that $\|XY\| \le \|X\|\,\|Y\|$. Let $S(X) = X^2$. Then
$$S(X + H) = X^2 + XH + HX + H^2,$$
and $\|H^2\| \le \|H\|^2 = o(\|H\|)$. So $DS(X)H = XH + HX$. This is not $2XH$, because matrices do not commute. For $X = \begin{pmatrix} 0 & 1 \\ 0 & 0\end{pmatrix}$ and $H = \begin{pmatrix} 0 & 0 \\ 1 & 0\end{pmatrix}$ one gets $XH = \begin{pmatrix} 1 & 0 \\ 0 & 0\end{pmatrix}$ and $HX = \begin{pmatrix} 0 & 0 \\ 0 & 1\end{pmatrix}$, so $DS(X)H = I$, while $2XH = \begin{pmatrix} 2 & 0 \\ 0 & 0\end{pmatrix}$. Chapter 2 proves the product rule in this form, for any normed algebra.

**Example (The norm squared in an inner product space).** Let $E$ be a real inner product space and $f(x) = \|x\|^2 = \langle x, x\rangle$. Then
$$\|x + h\|^2 = \|x\|^2 + 2\langle x, h\rangle + \|h\|^2.$$
The map $h \mapsto 2\langle x, h\rangle$ is linear and continuous with norm $2\|x\|$ by Cauchy-Schwarz, and $\|h\|^2 = o(\|h\|)$. So $Df(x)h = 2\langle x, h\rangle$.

::: mathlib
`hasStrictFDerivAt_norm_sq` · `Mathlib.Analysis.InnerProductSpace.Calculus`

`HasStrictFDerivAt (fun x => ‖x‖ ^ 2) (2 • innerSL ℝ x) x`. Here `innerSL ℝ x` is the continuous linear map $h \mapsto \langle x, h\rangle$.

<?decl hasStrictFDerivAt_norm_sq?>
:::

**Counterexample (The norm at $0$).** Let $E \neq \{0\}$ be a real normed space and $f(x) = \|x\|$. Suppose that $L$ is a derivative of $f$ at $0$. Then $\|h\| = Lh + r(h)$, and with $-h$ in place of $h$, $\|h\| = -Lh + r(-h)$. Adding the two equations gives $2\|h\| = r(h) + r(-h)$. For $\varepsilon = \frac12$ and small $h \neq 0$, the right side has absolute value at most $\|h\|$, and $2\|h\| \le \|h\|$ is false. So the norm is not differentiable at $0$. Away from $0$ the Euclidean norm is differentiable, with $D\|\cdot\|(x)h = \langle x, h\rangle/\|x\|$ by the chain rule of Chapter 2, while the norm $\max(|x|, |y|)$ of $\mathbb{R}^2$ is not differentiable at $(1, 1)$ (Exercise 3).

::: mathlib
`not_differentiableAt_norm_zero` · `Mathlib.Analysis.Calculus.FDeriv.Norm`

`¬DifferentiableAt ℝ (fun x => ‖x‖) 0` for a real normed space `E` with `[Nontrivial E]`.

<?decl not_differentiableAt_norm_zero?>
:::

### The library around it

The files `Mathlib.Analysis.Calculus.FDeriv.*` state each result in four forms: `HasFDerivAt`, `HasFDerivWithinAt`, `DifferentiableAt` and `fderiv`, with regular names such as `HasFDerivAt.continuousAt`, `DifferentiableAt.continuousAt` and `DifferentiableOn.continuousOn`. A proof works with `HasFDerivAt`, which records the derivative, and converts to `fderiv` at the end. The file `FDeriv.Const` gives constants and `FDeriv.Linear` gives continuous linear maps. The tactic `fun_prop` proves `DifferentiableAt 𝕜 f x` for an expression built from differentiable pieces.

Common errors of a learner:

- Forgetting the field. `fderiv ℝ f x` and `fderiv ℂ f x` are different objects, and `DifferentiableAt ℂ f x` is a much stronger statement than `DifferentiableAt ℝ f x`.
- Reading `fderiv 𝕜 f x = 0` as "$x$ is a critical point". It also holds where $f$ is not differentiable.
- Expecting `fderiv 𝕜 f x` to be a vector. It is a map `E →L[𝕜] F`, and `fderiv 𝕜 f x v` is its value at `v`.

### Exercises

1. (A) Let $f(x, y) = x^2 y + y^3$ on $\mathbb{R}^2$. Show from the definition that $Df(1, 2)(h, k) = 4h + 13k$. Hint: expand $f(1 + h, 2 + k)$.
2. (A) Let $T(X) = X^3$ on $M_n(\mathbb{R})$. Show that $DT(X)H = HX^2 + XHX + X^2H$.
3. (B) Show that the norm $\|(x, y)\|_\infty = \max(|x|, |y|)$ of $\mathbb{R}^2$ is differentiable at $(1, 0)$ and compute the derivative. Show that it is not differentiable at $(1, 1)$. Hint: near $(1, 0)$ the norm equals $x$.
4. (B) Let $f : E \to F$ be differentiable at $x$ and $A \in L(F, G)$. Show from the definition that $A \circ f$ is differentiable at $x$ with $D(A \circ f)(x) = A \circ Df(x)$.
5. (B) Let $E = C([0, 1])$ with the sup norm and $F(u) = u^2$, the pointwise square. Show that $F : E \to E$ is differentiable with $DF(u)h = 2uh$.
6. (C) Let $E$ be a real normed space and $f : E \to \mathbb{R}$ with $|f(x)| \le \|x\|^2$ for all $x$. Show that $f$ is differentiable at $0$ with $Df(0) = 0$. Give such an $f$ on $\mathbb{R}$ that is continuous only at $0$.

### Notes and history

The derivative as a linear map carries the name of Maurice Fréchet, who studied it for functionals on spaces of functions. The weaker notion of a derivative in each direction carries the name of René Gateaux, and Section 2 treats it. Dieudonné's *Foundations of Modern Analysis* (1960) made the coordinate-free derivative between Banach spaces the standard form of the calculus of several variables. Mathlib takes the same view: the derivative of one variable, the derivative within a set and the strict derivative are all variants of `HasFDerivAtFilter`.

### Reference

<?reference?>
