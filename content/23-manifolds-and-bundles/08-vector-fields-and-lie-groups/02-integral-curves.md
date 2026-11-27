---
title: Integral curves
kind: theory
modules:
  - Mathlib.Geometry.Manifold.IntegralCurve.Basic
  - Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
  - Mathlib.Geometry.Manifold.IntegralCurve.Transform
  - Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
explains:
  E3: [IsMIntegralCurveOn, IsMIntegralCurve, exists_isMIntegralCurveAt_of_contMDiffAt, isMIntegralCurveOn_Ioo_eqOn_of_contMDiff]
  E2: [IsMIntegralCurveAt, IsMIntegralCurveOn.hasDerivWithinAt, exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless, isMIntegralCurveAt_eventuallyEq_of_contMDiffAt, isMIntegralCurve_eq_of_contMDiff, IsMIntegralCurve.periodic_of_eq, IsMIntegralCurve.periodic_xor_injective, IsMIntegralCurve.comp_add, IsMIntegralCurve.comp_mul, isMIntegralCurve_const, isMIntegralCurveOn_piecewise, exists_isMIntegralCurve_of_isMIntegralCurveOn]
  E1: auto
families: []
requires: [V23.C04, V23.C05, V17.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Integral curves

### Overview

An integral curve of a vector field $v$ is a curve $\gamma$ with $\gamma'(t) = v(\gamma(t))$. In a chart this is an ordinary differential equation $u' = \tilde v(u)$, and the theorems of Volume 17, Chapter 8 apply: Picard and Lindelöf give a local solution, and the estimate of Grönwall makes it unique. This section transfers these two results to manifolds, glues local uniqueness into uniqueness on intervals, and proves two global facts: curves that exist for a uniform time extend to all of $\mathbb{R}$, and a global integral curve is periodic or injective.

Throughout, $M$ is a real $C^1$ manifold modelled on $(E, H, I)$, with $E$ a Banach space, and $v$ is a vector field on $M$.

### Definitions

**Definition (Integral curve).** Let $s \subseteq \mathbb{R}$. A map $\gamma : \mathbb{R} \to M$ is an *integral curve of $v$ on $s$* if for every $t \in s$ the map $\gamma$ has, within $s$ at $t$, the derivative $h \mapsto h\,v(\gamma(t))$ from $\mathbb{R}$ to $T_{\gamma(t)}M$. It is an integral curve *at* $t_0$ if this holds on a neighbourhood of $t_0$, and a *global* integral curve if it holds on $\mathbb{R}$.

**Definition (Local representative).** Let $\tilde\varphi$ be the extended chart at $x_0$. The *local representative* of $v$ is the map $\tilde v$ on $\tilde\varphi(\operatorname{dom}\tilde\varphi)$ given by $\tilde v(u) = D(\tilde\varphi \circ \tilde\psi_y^{-1})\,v(y)$, with $y = \tilde\varphi^{-1}(u)$ and $\tilde\psi_y$ the extended chart at $y$: the vector $v(y)$ written in the chart $\tilde\varphi$.

**Definition (Interior point).** A point $x$ is *interior* if $\tilde\varphi_x(x)$ lies in the interior of $\operatorname{range} I$. On a manifold without boundary every point is interior.

::: mathlib
`IsMIntegralCurveOn` · `Mathlib.Geometry.Manifold.IntegralCurve.Basic`

`IsMIntegralCurveOn γ v s` says `∀ t ∈ s, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ s t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))`. The derivative is the linear map $h \mapsto h\,v(\gamma(t))$. `IsMIntegralCurveAt γ v t₀` asks this on a neighbourhood of `t₀`, and `IsMIntegralCurve γ v` on all of `ℝ`. `IsMIntegralCurveOn.hasDerivWithinAt` gives the chart form, with the change of coordinates `tangentCoordChange`.

<?decl IsMIntegralCurveOn?>
<?decl IsMIntegralCurveAt?>
<?decl IsMIntegralCurve?>
<?decl IsMIntegralCurveOn.hasDerivWithinAt?>
:::

### Theorems and proofs

**Lemma (Chart form).** Let $\gamma(t)$ lie in $\operatorname{dom}\tilde\varphi$ for $t$ in an open interval $J$. Then $\gamma$ is an integral curve of $v$ on $J$ if and only if $\alpha = \tilde\varphi \circ \gamma$ satisfies $\alpha'(t) = \tilde v(\alpha(t))$ on $J$.

*Proof.* The derivative of $\gamma$ at $t$, in the charts $\mathrm{id}$ of $\mathbb{R}$ and $\tilde\psi_{\gamma(t)}$, is the derivative of $\tilde\psi_{\gamma(t)} \circ \gamma$. Composing with the change of charts $\tilde\varphi \circ \tilde\psi_{\gamma(t)}^{-1}$ and using the chain rule, the statement $(\tilde\psi_{\gamma(t)} \circ \gamma)'(t) = v(\gamma(t))$ becomes $\alpha'(t) = D(\tilde\varphi \circ \tilde\psi_{\gamma(t)}^{-1})\,v(\gamma(t)) = \tilde v(\alpha(t))$. The change of charts has invertible derivative, so the two statements are equivalent. $\square$

**Theorem (Local existence).** Let $E$ be complete, let $v$ be $C^1$ at $x_0$ as a map $M \to TM$, and let $x_0$ be an interior point. For every $t_0 \in \mathbb{R}$ there is an integral curve $\gamma$ of $v$ at $t_0$ with $\gamma(t_0) = x_0$.

*Proof.* Let $u_0 = \tilde\varphi(x_0)$ and let $\Omega$ be the interior of $\tilde\varphi(\operatorname{dom}\tilde\varphi)$, an open set of $E$ that contains $u_0$ because $x_0$ is interior. The smoothness of $v$ at $x_0$ means that $\tilde v$ is $C^1$ at $u_0$ on $\Omega$. A map that is $C^1$ at a point is Lipschitz on a ball around it. By the theorem of Picard and Lindelöf (Volume 17, Chapter 8) there are $\varepsilon > 0$ and $\alpha$ with $\alpha(t_0) = u_0$ and $\alpha'(t) = \tilde v(\alpha(t))$ for $|t - t_0| < \varepsilon$. The map $\alpha$ is continuous and $\Omega$ is open, so after shrinking $\varepsilon$, $\alpha(t) \in \Omega$ for these $t$. Put $\gamma = \tilde\varphi^{-1} \circ \alpha$. Then $\gamma(t_0) = x_0$, $\tilde\varphi \circ \gamma = \alpha$ near $t_0$, and the chart form shows that $\gamma$ is an integral curve at $t_0$. $\square$

**Theorem (Local uniqueness).** Let $v$ be $C^1$ at $\gamma(t_0)$, an interior point, and let $\gamma, \gamma'$ be integral curves at $t_0$ with $\gamma(t_0) = \gamma'(t_0)$. Then $\gamma = \gamma'$ near $t_0$.

*Proof.* Near $t_0$ both curves lie in $\operatorname{dom}\tilde\varphi$, with $\tilde\varphi$ the chart at $\gamma(t_0)$, and their representatives $\alpha, \beta$ lie in a closed ball $B \subseteq \Omega$ around $u_0$ on which $\tilde v$ is $K$-Lipschitz. By the chart form, both solve $u' = \tilde v(u)$ with $\alpha(t_0) = \beta(t_0)$. Then $\|(\alpha - \beta)'(t)\| \le K\|\alpha(t) - \beta(t)\|$, and the inequality of Grönwall gives $\|\alpha(t) - \beta(t)\| \le e^{K|t - t_0|}\,\|\alpha(t_0) - \beta(t_0)\| = 0$. So $\alpha = \beta$, and $\gamma = \gamma'$, near $t_0$. $\square$

**Theorem (Uniqueness on intervals).** Let $M$ be Hausdorff, $v$ a $C^1$ field, and $\gamma, \gamma'$ integral curves on $(a, b)$ with $\gamma(t) $ interior for all $t \in (a, b)$. If $\gamma(t_0) = \gamma'(t_0)$ for one $t_0 \in (a, b)$, then $\gamma = \gamma'$ on $(a, b)$.

*Proof.* Let $S = \{t \in (a, b) : \gamma(t) = \gamma'(t)\}$. It contains $t_0$. It is open by local uniqueness. It is closed in $(a, b)$: the curves are continuous, and the set where two continuous maps to a Hausdorff space agree is closed. The interval $(a, b)$ is connected, so $S = (a, b)$. $\square$

The Hausdorff hypothesis cannot be dropped. On the line with two origins, the field $\partial_x$ has two integral curves through $-1$ at time $0$ that agree for $t < 1$ and pass through different origins at $t = 1$.

**Lemma (Transformations).** Let $\gamma$ be a global integral curve of $v$. Then $t \mapsto \gamma(t + c)$ is a global integral curve of $v$ for every $c \in \mathbb{R}$, and $t \mapsto \gamma(at)$ is a global integral curve of $av$ for every $a \in \mathbb{R}$. If $v(x) = 0$, the constant curve at $x$ is a global integral curve.

*Proof.* By the chain rule, the derivative of $t \mapsto \gamma(t + c)$ at $t$ is $h \mapsto h\,v(\gamma(t + c))$, and that of $t \mapsto \gamma(at)$ is $h \mapsto ah\,v(\gamma(at))$. The constant curve has derivative $0 = h\,v(x)$. $\square$

**Theorem (Periodic or injective).** Let $M$ be Hausdorff without boundary, $v$ a $C^1$ field, and $\gamma$ a global integral curve. If $\gamma(a) = \gamma(b)$, then $\gamma$ is periodic with period $a - b$. Consequently, exactly one of two cases holds: $\gamma$ is injective, or $\gamma$ is periodic with a positive period.

*Proof.* Let $\beta(t) = \gamma(t + (a - b))$. By the lemma, $\beta$ is a global integral curve, and $\beta(b) = \gamma(a) = \gamma(b)$. By uniqueness on intervals, applied on every interval $(-n, n)$ that contains $b$, $\beta = \gamma$. So $\gamma(t + (a - b)) = \gamma(t)$ for all $t$. If $\gamma$ is not injective, choose $a \ne b$ with $\gamma(a) = \gamma(b)$; then $|a - b| > 0$ is a period, because a period of a map is also a period with the opposite sign. If $\gamma$ has a period $T > 0$, then $\gamma(0) = \gamma(T)$, so $\gamma$ is not injective. $\square$

**Theorem (Uniform time).** Let $M$ be Hausdorff without boundary and $v$ a $C^1$ field. Assume there is $\varepsilon > 0$ such that each $x \in M$ has an integral curve $\gamma_x$ on $(-\varepsilon, \varepsilon)$ with $\gamma_x(0) = x$. Then each $x$ has a global integral curve through $x$ at time $0$.

*Proof.* *Step 1: extension.* Let $\gamma$ be an integral curve on $(-r, r)$ with $r \ge \varepsilon$ and $\gamma(0) = x$. Put $t_1 = r - \varepsilon/2 \in (-r, r)$ and $\beta(t) = \gamma_{\gamma(t_1)}(t - t_1)$. By the lemma on transformations, $\beta$ is an integral curve on $(t_1 - \varepsilon, t_1 + \varepsilon)$, and $\beta(t_1) = \gamma(t_1)$. The two intervals overlap in an interval that contains $t_1$, so by uniqueness $\beta = \gamma$ on the overlap. The curve equal to $\gamma$ on $(-r, r)$ and to $\beta$ on $[r, r + \varepsilon/2)$ is then an integral curve on $(-r, r + \varepsilon/2)$, because near each point it agrees with $\gamma$ or with $\beta$ on an open interval. Do the same at $-r$, with $t_1 = -r + \varepsilon/2$. The result is an integral curve on $(-r - \varepsilon/2, r + \varepsilon/2)$ that extends $\gamma$.

*Step 2: the limit.* Start with $\gamma_x$ on $(-\varepsilon, \varepsilon)$ and apply Step 1 repeatedly. This gives curves $\gamma_n$ on $I_n = (-\varepsilon - n\varepsilon/2, \varepsilon + n\varepsilon/2)$, each extending the previous one. Define $\gamma(t) = \gamma_n(t)$ for any $n$ with $t \in I_n$. Near each $t$ the map $\gamma$ equals some $\gamma_n$ on an open interval, so it is a global integral curve, and $\gamma(0) = x$. $\square$

::: mathlib
`exists_isMIntegralCurveAt_of_contMDiffAt` · `Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique`

The existence theorem takes `t₀`, `[CompleteSpace E]`, `CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀` and `I.IsInteriorPoint x₀`. Its proof calls `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`, the local existence for an autonomous equation with a $C^1$ field. The variant `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless` replaces the interior point by `[BoundarylessManifold I M]`. Local uniqueness is `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt`.

<?decl exists_isMIntegralCurveAt_of_contMDiffAt?>
<?decl exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless?>
<?decl isMIntegralCurveAt_eventuallyEq_of_contMDiffAt?>
<?decl ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀?>
:::

::: mathlib
`isMIntegralCurveOn_Ioo_eqOn_of_contMDiff` · `Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique`

Uniqueness on `Set.Ioo a b` needs `[T2Space M]`, interior points along `γ`, a field that is `ContMDiff` of order `1` and `γ t₀ = γ' t₀`. The global form is `isMIntegralCurve_eq_of_contMDiff`. With `[BoundarylessManifold I M]`, `IsMIntegralCurve.periodic_of_eq` and `IsMIntegralCurve.periodic_xor_injective` give the dichotomy, stated with `Xor`.

<?decl isMIntegralCurveOn_Ioo_eqOn_of_contMDiff?>
<?decl isMIntegralCurve_eq_of_contMDiff?>
<?decl IsMIntegralCurve.periodic_xor_injective?>
<?decl IsMIntegralCurve.periodic_of_eq?>
:::

### Examples

**Example (Rotation).** On $\mathbb{R}^2$ let $v(x, y) = (-y, x)$. The curve $\gamma(t) = (r\cos(t + c), r\sin(t + c))$ satisfies $\gamma' = (-r\sin(t+c), r\cos(t+c)) = v(\gamma)$. Every global integral curve is of this form, by uniqueness. For $r > 0$ it is periodic with period $2\pi$. For $r = 0$ it is the constant curve at the zero of $v$, periodic with every period.

**Example (Blow-up).** On $\mathbb{R}$ let $v(x) = x^2$. The solution with $\gamma(0) = x_0 > 0$ is $\gamma(t) = x_0/(1 - t x_0)$ for $t < 1/x_0$. It tends to $\infty$ as $t \to 1/x_0$. By uniqueness no integral curve through $x_0$ extends past $1/x_0$, so no global integral curve passes through $x_0$. The uniform time theorem does not apply: the time of existence $1/x_0$ tends to $0$ as $x_0 \to \infty$.

**Example (A missing point).** On $M = \mathbb{R}^2 \setminus \{0\}$ let $v = \partial_x$. The curve through $(-1, 0)$ is $t \mapsto (t - 1, 0)$, and it reaches the missing origin at $t = 1$. So $v$ has no global integral curve through $(-1, 0)$, even though $v$ is bounded.

### The library around it

The file `Transform` has the lemmas of translation and rescaling, with variants for curves on sets and at points. The file `UniformTime` proves the uniform time theorem as `exists_isMIntegralCurve_of_isMIntegralCurveOn`, citing Lemma 9.15 of the book of Lee, and the gluing step as `isMIntegralCurveOn_piecewise`. The index of this edition has no declaration for the flow of a vector field and no declaration that a $C^1$ vector field on a compact manifold has global integral curves.

::: mathlib
`exists_isMIntegralCurve_of_isMIntegralCurveOn` · `Mathlib.Geometry.Manifold.IntegralCurve.UniformTime`

The hypothesis asks curves on `Ioo (-ε) ε` through every point, with `0 < ε`, on a manifold with `[T2Space M]` and `[BoundarylessManifold I M]`.

<?decl exists_isMIntegralCurve_of_isMIntegralCurveOn?>
<?decl isMIntegralCurveOn_piecewise?>
<?decl IsMIntegralCurve.comp_add?>
<?decl IsMIntegralCurve.comp_mul?>
<?decl isMIntegralCurve_const?>
:::

Common errors of a learner:

- Forgetting the interior point hypothesis. At a boundary point the field can point outward, and then no integral curve starts there.
- Expecting uniqueness without `T2Space`. The line with two origins is a counterexample.

### Exercises

1. (A) Find all integral curves of $v(x) = x$ on $\mathbb{R}$ and check that they are global.
2. (A) Let $\gamma$ be an integral curve of $v$ with $\gamma(t_0) = x$ and $v(x) = 0$. Show that $\gamma$ is constant. Hint: compare with the constant curve.
3. (B) Show that the integral curves of $v(x, y) = (x, -y)$ on $\mathbb{R}^2$ are global and injective, except for one. Hint: solve the two equations separately.
4. (B) Let $v$ be $C^1$ on $\mathbb{R}^n$ with $\|v(x)\| \le C(1 + \|x\|)$. Show that all integral curves are global. Hint: Grönwall bounds $\|\gamma(t)\|$ on bounded intervals.
5. (B) On the half-line $M = [0, \infty)$ with the boundary point $0$, let $v(x) = -1$. Show that no integral curve at $t_0 = 0$ passes through $0$ at time $0$. Hint: such a curve would satisfy $\gamma(t) = -t$ for small $t > 0$.
6. (C) Let $M$ be compact, Hausdorff and without boundary, and $v$ a $C^1$ field. Prove that every point has a global integral curve. Hint: in the proof of local existence, Picard and Lindelöf give a time $\varepsilon_x$ that works for all points of a neighbourhood of $x$; cover $M$ by finitely many such neighbourhoods and apply the uniform time theorem.
7. (C) Show that the period set $\{T : \gamma(t + T) = \gamma(t) \text{ for all } t\}$ of a global integral curve is a closed subgroup of $\mathbb{R}$, and deduce that a nonconstant periodic curve has a smallest positive period. Hint: a closed subgroup of $\mathbb{R}$ other than $\mathbb{R}$ is $c\mathbb{Z}$ for some $c \ge 0$.

### Notes and history

The theorem of existence and uniqueness for Lipschitz fields carries the names of Cauchy, Lipschitz, Picard and Lindelöf. Peano proved existence, without uniqueness, for continuous fields. The Mathlib files cite the book of Lee, *Introduction to smooth manifolds*, for the uniform time lemma. The existence of integral curves through boundary points is listed in the files as future work.

### Reference

<?reference?>
