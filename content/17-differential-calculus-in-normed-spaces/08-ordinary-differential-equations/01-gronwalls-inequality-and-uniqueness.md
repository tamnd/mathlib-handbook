---
title: Grönwall's inequality and the uniqueness of solutions
kind: theory
modules:
  - Mathlib.Analysis.ODE.Basic
  - Mathlib.Analysis.ODE.Gronwall
  - Mathlib.Analysis.ODE.DiscreteGronwall
  - Mathlib.Analysis.ODE.Transform
explains:
  E3: [IsIntegralCurveOn, gronwallBound, norm_le_gronwallBound_of_norm_deriv_right_le, ODE_solution_unique]
  E2: [IsIntegralCurve, IsIntegralCurveAt, gronwallBound_of_K_ne_0, gronwallBound_ε0, hasDerivAt_gronwallBound, dist_le_of_trajectories_ODE, dist_le_of_approx_trajectories_ODE, ODE_solution_unique_of_mem_Icc, ODE_solution_unique_univ, discrete_gronwall, IsIntegralCurveOn.comp_mul]
  E1: auto
families: []
requires: [V13.C03, V15.C03, V15.C05, V17.C01, V17.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Grönwall's inequality and the uniqueness of solutions

### Overview

An ordinary differential equation $x' = v(t, x)$ asks for a curve whose velocity is given by a vector field. Before existence, which Section 2 proves, comes control: Grönwall's inequality bounds how far two solutions drift apart. If a curve $u$ satisfies $\|u'\| \le K\|u\| + \varepsilon$, then $\|u\|$ grows at most as fast as the solution of the scalar equation $y' = Ky + \varepsilon$. Applied to the difference of two solutions of an equation with a field that is $K$-Lipschitz in $x$, it gives
$$\|x(t) - y(t)\| \le \|x(a) - y(a)\|\, e^{K(t - a)}.$$
So two solutions with the same initial value are equal, and the solution depends continuously on its initial value.

The example $x' = \sqrt{|x|}$ shows that uniqueness fails without the Lipschitz condition.

### Definitions

Throughout, $E$ is a real normed space and $v : \mathbb{R} \times E \to E$ is a *time-dependent vector field*. A field that does not depend on $t$ is *autonomous*.

**Definition (Integral curve).** Let $s \subseteq \mathbb{R}$. A curve $\gamma : \mathbb{R} \to E$ is an *integral curve of $v$ on $s$* if for each $t \in s$ the curve $\gamma$ has the derivative $v(t, \gamma(t))$ at $t$ within $s$. It is an *integral curve at $t_0$* if it is an integral curve on some neighbourhood of $t_0$, and a *global integral curve* if it is an integral curve on $\mathbb{R}$. The *initial value problem* with the data $(t_0, x_0)$ asks for an integral curve $\gamma$ on an interval that contains $t_0$, with $\gamma(t_0) = x_0$.

::: mathlib
`IsIntegralCurveOn` · `Mathlib.Analysis.ODE.Basic`

`IsIntegralCurveOn γ v s` says that `HasDerivWithinAt γ (v t (γ t)) s t` for each `t ∈ s`. The field has the type `ℝ → E → E`, time first. `IsIntegralCurveAt γ v t₀` and `IsIntegralCurve γ v` are the local and the global forms.

<?decl IsIntegralCurveOn?>
:::

**Definition (Lipschitz field).** The field $v$ is *$K$-Lipschitz in $x$* on a set $S \subseteq E$ if $\|v(t, x) - v(t, y)\| \le K\|x - y\|$ for all $t$ in the time interval and all $x, y \in S$.

By the mean value inequality of Chapter 3, a $C^1$ field is Lipschitz in $x$ on $J \times \bar B$ for a compact interval $J$ and a closed ball $\bar B$, with $K = \sup_{J \times \bar B} \|D_x v\|$.

**Definition (The Grönwall function).** For real numbers $\delta$, $K$ and $\varepsilon$ let
$$B_{\delta, K, \varepsilon}(x) = \delta e^{Kx} + \frac{\varepsilon}{K}\big(e^{Kx} - 1\big) \quad (K \ne 0), \qquad B_{\delta, 0, \varepsilon}(x) = \delta + \varepsilon x.$$

::: mathlib
`gronwallBound` · `Mathlib.Analysis.ODE.Gronwall`

`gronwallBound δ K ε x` is $B_{\delta, K, \varepsilon}(x)$. The definition is by cases on `K = 0`, and the lemmas `gronwallBound_of_K_ne_0`, `gronwallBound_K0` and `gronwallBound_ε0` give the closed forms. The last one is `gronwallBound δ K 0 x = δ * Real.exp (K * x)`, the case of exact solutions.

<?decl gronwallBound?>
:::

### Theorems and proofs

**Lemma (The Grönwall function solves the comparison equation).** For all $\delta, K, \varepsilon$ the function $B = B_{\delta, K, \varepsilon}$ satisfies $B(0) = \delta$ and $B'(x) = K B(x) + \varepsilon$ for all $x$.

*Proof.* For $K = 0$, $B(x) = \delta + \varepsilon x$, so $B(0) = \delta$ and $B' = \varepsilon = 0 \cdot B + \varepsilon$. For $K \ne 0$, $B(0) = \delta + \frac{\varepsilon}{K}(1 - 1) = \delta$. The derivative of $e^{Kx}$ is $K e^{Kx}$ (Volume 15, Chapter 5), so
$$B'(x) = K\delta e^{Kx} + \varepsilon e^{Kx} = K\Big(\delta e^{Kx} + \frac{\varepsilon}{K}(e^{Kx} - 1)\Big) + \varepsilon = K B(x) + \varepsilon. \qquad \square$$

::: mathlib
`hasDerivAt_gronwallBound` · `Mathlib.Analysis.ODE.Gronwall`

The lemma: `HasDerivAt (gronwallBound δ K ε) (K * gronwallBound δ K ε x + ε) x`. The shifted form `hasDerivAt_gronwallBound_shift` is for $x \mapsto B(x - a)$, which the inequality below uses.

<?decl hasDerivAt_gronwallBound?>
:::

**Theorem (Grönwall's inequality).** Let $f : [a, b] \to E$ be continuous, and let $f$ have a right derivative $f'(x)$ at each $x \in [a, b)$. Assume $\|f(a)\| \le \delta$ and
$$\|f'(x)\| \le K\|f(x)\| + \varepsilon \quad \text{for all } x \in [a, b).$$
Then $\|f(x)\| \le B_{\delta, K, \varepsilon}(x - a)$ for all $x \in [a, b]$.

*Proof.* Compare $u(x) = \|f(x)\|$ with a barrier that grows strictly faster than the inequality allows.

Step 1. Fix $\eta > 0$ and let $\beta(x) = B_{\delta + \eta, K, \varepsilon + \eta}(x - a)$. By the lemma, $\beta(a) = \delta + \eta$ and $\beta'(x) = K\beta(x) + \varepsilon + \eta$. The function $u$ is continuous, as the norm of a continuous function.

Step 2. Let $S = \{x \in [a, b] : u(y) \le \beta(y) \text{ for all } y \in [a, x]\}$. It contains $a$, because $u(a) \le \delta < \beta(a)$. It is a closed interval that starts at $a$, because $u - \beta$ is continuous. Let $c = \max S$. Suppose that $c < b$. Two cases arise.

Case $u(c) < \beta(c)$. By continuity $u < \beta$ on $[c, c + h_0]$ for some $h_0 > 0$, so $c + h_0 \in S$. This contradicts the choice of $c$.

Case $u(c) = \beta(c)$. For $h > 0$ the triangle inequality gives
$$\frac{u(c + h) - u(c)}{h} \le \frac{\|f(c + h) - f(c)\|}{h} \xrightarrow[h \to 0^+]{} \|f'(c)\| \le K u(c) + \varepsilon = K\beta(c) + \varepsilon.$$
The slope of $\beta$ tends to $\beta'(c) = K\beta(c) + \varepsilon + \eta$, which is larger by $\eta$. So for all small $h > 0$ the slope of $u$ is less than the slope of $\beta$, and since $u(c) = \beta(c)$, this gives $u(c + h) < \beta(c + h)$. Then $u \le \beta$ on $[a, c + h_0]$ for some $h_0 > 0$, a contradiction again.

So $c = b$, and $u \le \beta$ on $[a, b]$.

Step 3. For fixed $x$, the value $B_{\delta + \eta, K, \varepsilon + \eta}(x - a)$ is a continuous function of $\eta$, by the closed formula. Let $\eta \to 0^+$ in $u(x) \le \beta(x)$. $\square$

The proof needs no sign condition on $K$, and it never differentiates $u = \|f\|$, which may have no derivative where $f = 0$.

::: mathlib
`norm_le_gronwallBound_of_norm_deriv_right_le` · `Mathlib.Analysis.ODE.Gronwall`

The theorem, with the hypotheses `ContinuousOn f (Set.Icc a b)`, `HasDerivWithinAt f (f' x) (Set.Ici x) x` for `x ∈ Set.Ico a b` (the right derivative), `‖f a‖ ≤ δ` and `‖f' x‖ ≤ K * ‖f x‖ + ε`. Its proof goes through `image_le_of_liminf_slope_right_lt_deriv_boundary` of `Mathlib.Analysis.Calculus.MeanValue`, which is Step 2 above.

<?decl norm_le_gronwallBound_of_norm_deriv_right_le?>
:::

**Theorem (Distance of two solutions).** Let $v$ be $K$-Lipschitz in $x$ on $E$ for each $t \in [a, b]$. Let $f$ and $g$ be continuous on $[a, b]$ and integral curves of $v$ on $[a, b)$, with right derivatives, and let $\|f(a) - g(a)\| \le \delta$. Then
$$\|f(t) - g(t)\| \le \delta\, e^{K(t - a)} \quad \text{for all } t \in [a, b].$$

*Proof.* The curve $w = f - g$ is continuous with the right derivative $w'(t) = v(t, f(t)) - v(t, g(t))$ at each $t \in [a, b)$. By the Lipschitz condition $\|w'(t)\| \le K\|f(t) - g(t)\| = K\|w(t)\|$. Grönwall's inequality with $\varepsilon = 0$ gives $\|w(t)\| \le B_{\delta, K, 0}(t - a) = \delta e^{K(t - a)}$. $\square$

::: mathlib
`dist_le_of_trajectories_ODE` · `Mathlib.Analysis.ODE.Gronwall`

The theorem with `dist (f a) (g a) ≤ δ` and the conclusion `dist (f t) (g t) ≤ δ * Real.exp (K * (t - a))`. The Lipschitz hypothesis is `∀ t, LipschitzWith K (v t)` with `K : ℝ≥0`.

<?decl dist_le_of_trajectories_ODE?>
:::

**Theorem (Uniqueness).** Under the hypotheses of the last theorem, if $f(a) = g(a)$, then $f = g$ on $[a, b]$. If $v$ is $K$-Lipschitz in $x$ for all $t \in \mathbb{R}$, two global integral curves that agree at one time $t_0$ are equal.

*Proof.* The first claim is the last theorem with $\delta = 0$. For the second, the first claim gives $f = g$ on $[t_0, b]$ for each $b > t_0$. For the times before $t_0$, let $\tilde f(t) = f(-t)$ and $\tilde g(t) = g(-t)$. By the chain rule they are integral curves of the field $\tilde v(t, x) = -v(-t, x)$, which is also $K$-Lipschitz in $x$, and they agree at $-t_0$. The first claim gives $\tilde f = \tilde g$ on $[-t_0, \infty)$, so $f = g$ on $(-\infty, t_0]$. $\square$

::: mathlib
`ODE_solution_unique` · `Mathlib.Analysis.ODE.ExistUnique`

The first claim: `Set.EqOn f g (Set.Icc a b)` from `f a = g a`. Its relatives are `ODE_solution_unique_of_mem_Icc`, with an initial time inside `Ioo a b`, and `ODE_solution_unique_univ` for global curves. The time reversal of the proof is `IsIntegralCurveOn.comp_mul` with the factor $-1$, in `Mathlib.Analysis.ODE.Transform`.

<?decl ODE_solution_unique?>
:::

**Theorem (Approximate solutions).** Let $v$ be $K$-Lipschitz in $x$. Let $f$ and $g$ be continuous on $[a, b]$ with right derivatives $f'$, $g'$ on $[a, b)$ such that $\|f'(t) - v(t, f(t))\| \le \varepsilon_f$ and $\|g'(t) - v(t, g(t))\| \le \varepsilon_g$. If $\|f(a) - g(a)\| \le \delta$, then $\|f(t) - g(t)\| \le B_{\delta, K, \varepsilon_f + \varepsilon_g}(t - a)$ on $[a, b]$.

*Proof.* For $w = f - g$ the triangle inequality gives
$$\|w'(t)\| \le \|f'(t) - v(t, f(t))\| + \|v(t, f(t)) - v(t, g(t))\| + \|v(t, g(t)) - g'(t)\| \le \varepsilon_f + K\|w(t)\| + \varepsilon_g.$$
Grönwall's inequality gives the claim. $\square$

::: mathlib
`dist_le_of_approx_trajectories_ODE` · `Mathlib.Analysis.ODE.Gronwall`

The theorem, with the bounds `dist (f' t) (v t (f t)) ≤ εf` and the conclusion `dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a)`.

<?decl dist_le_of_approx_trajectories_ODE?>
:::

### Examples

**Example (The sine field).** Let $E = \mathbb{R}$ and $v(t, x) = \sin x$. By the mean value theorem $|\sin x - \sin y| \le |x - y|$, so $K = 1$. The constant curve $0$ is a solution. Let $x$ be the solution with $x(0) = 0.01$ (it exists by Section 2). The distance theorem gives $|x(t)| \le 0.01\, e^{t}$ for $t \ge 0$. While $x$ is small, $\sin x \approx x$ and the bound is close to the truth. For large $t$ it is poor: $x(t)$ stays below the constant solution $\pi$, by uniqueness.

**Example (Linear equations).** Let $E = \mathbb{R}^n$ with a norm and let $A$ be an $n \times n$ matrix. The field $v(t, x) = Ax$ is $\|A\|$-Lipschitz, with the operator norm of Volume 16. By uniqueness $t \mapsto e^{tA}x_0$ is the only solution with the value $x_0$ at $0$. For a rotation matrix the bound is $e^{t}\|x(0) - y(0)\|$, while the true distance is constant.

**Counterexample (A field that is not Lipschitz).** Let $v(t, x) = \sqrt{|x|}$ on $\mathbb{R}$, with $x(0) = 0$. The constant $0$ is a solution. For each $c \ge 0$ the curve
$$x_c(t) = 0 \ (t \le c), \qquad x_c(t) = \tfrac14 (t - c)^2 \ (t \ge c)$$
is also a solution: for $t > c$, $x_c'(t) = \frac12(t - c) = \sqrt{x_c(t)}$, and at $t = c$ both one-sided derivatives are $0$. So the problem has infinitely many solutions. The field is continuous but not Lipschitz near $0$.

### The library around it

The files of `Mathlib.Analysis.ODE` have one pattern. A statement on $[a, b]$ uses `ContinuousOn` on `Set.Icc a b` and right derivatives `HasDerivWithinAt _ _ (Set.Ici t) t` on `Set.Ico a b`. A statement with `_of_mem` assumes the Lipschitz condition only on sets `s t` that the curves stay in. `Mathlib.Analysis.ODE.Transform` shifts time with `IsIntegralCurve.comp_add` and rescales it with `IsIntegralCurveOn.comp_mul`. `Mathlib.Analysis.ODE.DiscreteGronwall` has the discrete inequality `discrete_gronwall`: from $u_{n+1} \le (1 + c_n)u_n + b_n$ with $c_n, b_n \ge 0$ it gives $u_n \le (u_{n_0} + \sum b_k)\exp(\sum c_k)$, the form used for the error of Euler's method.

Common errors of a learner:

- Expecting uniqueness for every continuous field. Continuity gives existence (Peano's theorem) but not uniqueness, as $\sqrt{|x|}$ shows. Mathlib needs `LipschitzWith` or `LipschitzOnWith`.
- Writing the field as `E → E`. The field of `IsIntegralCurveOn` is `ℝ → E → E`, and an autonomous field needs `fun _ => f`.

### Exercises

1. (A) Compute $B_{1, 2, 3}(x)$ and check that it solves $y' = 2y + 3$, $y(0) = 1$.
2. (A) Let $f : [0, 1] \to \mathbb{R}^2$ be differentiable with $\|f'(t)\| \le 2\|f(t)\|$ and $f(0) = 0$. Show that $f = 0$.
3. (B) Let $v$ be $K$-Lipschitz in $x$ and let $f$, $g$ be global integral curves. Show that $\|f(t) - g(t)\| \le e^{K|t - t_0|}\|f(t_0) - g(t_0)\|$ for all $t$. Hint: time reversal.
4. (B) Let $u : [0, T] \to [0, \infty)$ be continuous with $u(t) \le \delta + K\int_0^t u(s)\,ds$ and $K \ge 0$. Prove $u(t) \le \delta e^{Kt}$, the integral form of Grönwall's inequality. Hint: apply the theorem to $U(t) = \delta + K\int_0^t u$, which satisfies $U' = Ku \le KU$.
5. (C) Euler's method with the step $h$ for $x' = v(t, x)$ defines the polygon $p$ with $p(t_{k+1}) = p(t_k) + h\, v(t_k, p(t_k))$, $t_k = a + kh$. Assume $\|v\| \le L$ and that $v$ is $K$-Lipschitz in $x$ and in $t$. Show that $\|p'(t) - v(t, p(t))\| \le K(1 + L)h$ for $t \in [t_k, t_{k+1})$, and deduce that $\|p(t) - x(t)\| \le (1 + L)h\,(e^{K(t - a)} - 1)$ for the exact solution $x$ with $x(a) = p(a)$.

### Notes and history

T. H. Grönwall proved the inequality in 1919, in a paper on the dependence of solutions on parameters, and R. Bellman gave the integral form in 1943. Peano proved that a continuous field on $\mathbb{R}^n$ always has a local solution.

### Reference

<?reference?>
