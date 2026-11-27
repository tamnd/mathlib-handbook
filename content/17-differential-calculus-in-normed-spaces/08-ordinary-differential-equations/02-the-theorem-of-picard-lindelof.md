---
title: The theorem of Picard-Lindelöf
kind: theory
modules:
  - Mathlib.Analysis.ODE.PicardLindelof
  - Mathlib.Analysis.ODE.ExistUnique
explains:
  E3: [IsPicardLindelof, ODE.picard, IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt]
  E2: [ODE.picard_apply, ODE.hasDerivWithinAt_picard_Icc, ODE.FunSpace, ODE.FunSpace.next, ODE.FunSpace.exists_contractingWith_iterate_next, ODE.FunSpace.exists_isFixedPt_next, IsPicardLindelof.exists_eq_forall_mem_Icc_eq_picard, IsPicardLindelof.of_time_independent, IsPicardLindelof.of_contDiffAt_one, IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith, ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt]
  E1: auto
families: []
requires: [V13.C03, V15.C05, V17.C01, V17.C03, V17.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The theorem of Picard-Lindelöf

### Overview

Section 1 proved that the problem $x' = v(t, x)$, $x(t_0) = x_0$ has at most one solution when $v$ is Lipschitz in $x$. This section proves that it has one, on a time interval that depends on the size of $v$ near $x_0$. This is the theorem of Picard-Lindelöf, also called the theorem of Cauchy-Lipschitz.

A solution is a fixed point of the Picard map $T\alpha = x_0 + \int_{t_0}^t v(\tau, \alpha(\tau))\,d\tau$. The $n$-th iterate of $T$ contracts distances by the factor $(Kh)^n/n!$, so the contraction principle gives the fixed point.

### Definitions

The proof uses two facts on the integral of a continuous curve $g : [\alpha, \beta] \to E$ with values in a Banach space, which Volume 18 proves. For $t_0, t \in [\alpha, \beta]$:

- (I1) the map $t \mapsto \int_{t_0}^t g(\tau)\,d\tau$ has the derivative $g(t)$ within $[\alpha, \beta]$ at each $t$ (the fundamental theorem of calculus);
- (I2) $\big\|\int_{t_0}^t g\big\| \le \big|\int_{t_0}^t \|g\|\big|$.

**Definition (The Picard map).** Let $v$ be a time-dependent field, $t_0 \in \mathbb{R}$ and $x \in E$. For a curve $\alpha$ such that $\tau \mapsto v(\tau, \alpha(\tau))$ is continuous, the *Picard map* is
$$(T\alpha)(t) = x + \int_{t_0}^t v(\tau, \alpha(\tau))\,d\tau.$$

::: mathlib
`ODE.picard` · `Mathlib.Analysis.ODE.PicardLindelof`

`ODE.picard f t₀ x₀ α` is the curve `fun t => x₀ + ∫ τ in t₀..t, f τ (α τ)`, by `ODE.picard_apply`. The interval integral is oriented, so times before `t₀` need no case split.

<?decl ODE.picard?>
:::

**Definition (Picard-Lindelöf data).** Let $t_{\min} \le t_0 \le t_{\max}$, let $x_0 \in E$ and let $a, r, L, K \ge 0$ be real numbers. Write $J = [t_{\min}, t_{\max}]$ and $\bar B = \bar B(x_0, a)$. The field $v$ *satisfies the Picard-Lindelöf conditions* with these constants if

1. for each $t \in J$, the map $v(t, \cdot)$ is $K$-Lipschitz on $\bar B$;
2. for each $x \in \bar B$, the map $t \mapsto v(t, x)$ is continuous on $J$;
3. $\|v(t, x)\| \le L$ for all $t \in J$ and $x \in \bar B$;
4. $L \cdot h \le a - r$, where $h = \max(t_{\max} - t_0,\ t_0 - t_{\min})$.

Condition 4 keeps a solution in $\bar B$: it starts within $r$ of $x_0$ and moves with a speed at most $L$, so in the time $h$ it moves at most $Lh \le a - r$.

::: mathlib
`IsPicardLindelof` · `Mathlib.Analysis.ODE.PicardLindelof`

`IsPicardLindelof f t₀ x₀ a r L K` is a structure of type `Prop` with the four fields of the definition. The constants have the type `ℝ≥0`, and `t₀` has the type `Set.Icc tmin tmax`.

<?decl IsPicardLindelof?>
:::

### Theorems and proofs

**Lemma (The integral equation).** Let the field satisfy conditions 1 and 2. Let $\alpha : J \to \bar B$ be continuous. Then $\tau \mapsto v(\tau, \alpha(\tau))$ is continuous on $J$, and the following are equivalent: (a) $\alpha(t_0) = x$ and $\alpha$ has the derivative $v(t, \alpha(t))$ within $J$ at each $t \in J$; (b) $\alpha = T\alpha$ on $J$.

*Proof.* Continuity: for $\sigma, \tau \in J$,
$$\|v(\tau, \alpha(\tau)) - v(\sigma, \alpha(\sigma))\| \le \|v(\tau, \alpha(\tau)) - v(\tau, \alpha(\sigma))\| + \|v(\tau, \alpha(\sigma)) - v(\sigma, \alpha(\sigma))\| \le K\|\alpha(\tau) - \alpha(\sigma)\| + \|v(\tau, \alpha(\sigma)) - v(\sigma, \alpha(\sigma))\|.$$
As $\tau \to \sigma$, the first term tends to $0$ because $\alpha$ is continuous, and the second because of condition 2 at the point $\alpha(\sigma)$.

(b) implies (a): $T\alpha(t_0) = x$, and by (I1) the derivative of $T\alpha$ within $J$ is $v(t, \alpha(t))$. (a) implies (b): the curve $\alpha - T\alpha$ has the derivative $0$ within $J$ at each point of the interval $J$, by (I1). By the mean value inequality of Chapter 3 it is constant on $J$. At $t_0$ its value is $x - x = 0$. $\square$

::: mathlib
`ODE.hasDerivWithinAt_picard_Icc` · `Mathlib.Analysis.ODE.PicardLindelof`

The direction (b) implies (a) for the derivative: if `uncurry f` is continuous on `Icc tmin tmax ×ˢ u` and `α` is continuous with values in `u`, then `picard f t₀ x₀ α` has the derivative `f t (α t)` within `Icc tmin tmax`.

<?decl ODE.hasDerivWithinAt_picard_Icc?>
:::

**Theorem (The contraction principle).** Let $X$ be a nonempty complete metric space and $S : X \to X$ a map with $d(Sx, Sy) \le q\, d(x, y)$ for some $q < 1$. Then $S$ has exactly one fixed point. If only some iterate $S^n$ satisfies this condition, the conclusion still holds.

*Proof.* Uniqueness: if $Sx = x$ and $Sy = y$, then $d(x, y) \le q\, d(x, y)$, so $d(x, y) = 0$. Existence: fix $x_0$ and let $x_k = S^k x_0$. By induction $d(x_k, x_{k+1}) \le q^k d(x_0, x_1)$, so for $m > k$
$$d(x_k, x_m) \le \sum_{j = k}^{m - 1} q^j d(x_0, x_1) \le \frac{q^k}{1 - q} d(x_0, x_1).$$
So $(x_k)$ is a Cauchy sequence, with a limit $y$. The map $S$ is continuous, so $Sy = \lim x_{k+1} = y$.

For the second claim, let $y$ be the unique fixed point of $S^n$. Then $S^n(Sy) = S(S^n y) = Sy$, so $Sy$ is also a fixed point of $S^n$, and $Sy = y$ by uniqueness. A fixed point of $S$ is a fixed point of $S^n$, so it is unique. $\square$

::: mathlib
`ContractingWith.fixedPoint` · `Mathlib.Topology.MetricSpace.Contracting`

`ContractingWith K f` says `K < 1` and `LipschitzWith K f`. For a nonempty complete space, `ContractingWith.fixedPoint f hf` is the fixed point and `ContractingWith.fixedPoint_isFixedPt` proves that it is fixed.

<?decl ContractingWith.fixedPoint?>
:::

**Theorem (Picard-Lindelöf).** Let $E$ be a Banach space and let $v$ satisfy the Picard-Lindelöf conditions with the constants $t_0, x_0, a, r, L, K$. Then for each $x \in \bar B(x_0, r)$ there is a curve $\alpha : J \to E$ with $\alpha(t_0) = x$ that has the derivative $v(t, \alpha(t))$ within $J$ at each $t \in J$. It is $L$-Lipschitz, it stays in $\bar B(x_0, a)$, and it is unique among the solutions with values in $\bar B(x_0, a)$.

*Proof.* Step 1: the space. Let $X$ be the set of $L$-Lipschitz curves $\alpha : J \to E$ with $\alpha(t_0) = x$, with the metric $d(\alpha, \beta) = \sup_J \|\alpha - \beta\|$. A uniform limit of such curves is again in $X$, and the continuous curves on $J$ form a complete space because $E$ is complete, so $X$ is complete. It contains the constant curve $x$. Each $\alpha \in X$ stays in $\bar B$:
$$\|\alpha(t) - x_0\| \le \|\alpha(t) - x\| + \|x - x_0\| \le L|t - t_0| + r \le Lh + r \le a.$$

Step 2: $T$ maps $X$ to $X$. Let $\alpha \in X$. By the lemma, $T\alpha$ is defined, and $T\alpha(t_0) = x$. By (I2) and condition 3, $\|T\alpha(t) - T\alpha(s)\| = \big\|\int_s^t v(\tau, \alpha(\tau))\,d\tau\big\| \le L|t - s|$.

Step 3: the iterates. For $\alpha, \beta \in X$, $n \ge 0$ and $t \in J$, the claim is
$$\|T^n\alpha(t) - T^n\beta(t)\| \le \frac{(K|t - t_0|)^n}{n!}\, d(\alpha, \beta).$$
For $n = 0$ it is the definition of $d$. If it holds for $n$, then by (I2) and condition 1, for $t \ge t_0$,
$$\|T^{n+1}\alpha(t) - T^{n+1}\beta(t)\| \le \int_{t_0}^t K\,\|T^n\alpha(\tau) - T^n\beta(\tau)\|\,d\tau \le K\int_{t_0}^t \frac{K^n(\tau - t_0)^n}{n!}\,d\tau\; d(\alpha, \beta) = \frac{(K(t - t_0))^{n+1}}{(n+1)!}\, d(\alpha, \beta),$$
and the case $t < t_0$ is the same with $|\tau - t_0|$. So $d(T^n\alpha, T^n\beta) \le \frac{(Kh)^n}{n!}\, d(\alpha, \beta)$.

Step 4: the fixed point. The terms $(Kh)^n/n!$ of the series of $e^{Kh}$ tend to $0$, so $T^n$ is a contraction of $X$ for some $n$. By the contraction principle $T$ has a fixed point $\alpha \in X$, and by the lemma $\alpha$ is a solution. Uniqueness in $\bar B$ is the theorem of Section 1, in both directions of time. $\square$

::: mathlib
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` · `Mathlib.Analysis.ODE.ExistUnique`

The theorem: from `IsPicardLindelof f t₀ x₀ a r L K` and `x ∈ closedBall x₀ r` it gives `α` with `α t₀ = x` and `HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t` for `t ∈ Icc tmin tmax`. The integral form `IsPicardLindelof.exists_eq_forall_mem_Icc_eq_picard` gives `α t = picard f t₀ x α t`. The space of Step 1 is `ODE.FunSpace t₀ x₀ r L`, and `ODE.FunSpace.next` is the Picard map on it. Step 3 is `ODE.FunSpace.exists_contractingWith_iterate_next`, and Step 4 is `ODE.FunSpace.exists_isFixedPt_next`.

<?decl IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt?>
:::

The solutions depend continuously on the initial value: for two initial values $x, y \in \bar B(x_0, r)$ the distance theorem of Section 1 gives $\|\alpha_x(t) - \alpha_y(t)\| \le e^{K|t - t_0|}\|x - y\|$, since both curves stay in $\bar B$. Mathlib states this as `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`.

**Theorem (Local flows of $C^1$ fields).** Let $E$ be a Banach space and let $f : E \to E$ be $C^1$ near $x_0$. Then there are $r > 0$ and $\varepsilon > 0$ such that for each $x \in \bar B(x_0, r)$ and each $t_0$ there is a curve $\alpha$ with $\alpha(t_0) = x$ and $\alpha'(t) = f(\alpha(t))$ for $|t - t_0| < \varepsilon$.

*Proof.* Continuity of $Df$ at $x_0$ gives $a > 0$ with $\|Df\| \le K := \|Df(x_0)\| + 1$ on $\bar B(x_0, a)$. By the mean value inequality of Chapter 3, $f$ is $K$-Lipschitz on this ball, and $\|f\| \le L := \|f(x_0)\| + Ka$ there. With $r = a/2$ and $L\varepsilon \le a/2$ the Picard-Lindelöf conditions hold on $[t_0 - \varepsilon, t_0 + \varepsilon]$. $\square$

::: mathlib
`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` · `Mathlib.Analysis.ODE.ExistUnique`

The theorem, from `ContDiffAt ℝ 1 f x₀`. The intermediate step is `IsPicardLindelof.of_contDiffAt_one`, which produces the constants and the structure for all `t₀`. The class `ContDiffAt` is the one of Chapter 4.

<?decl ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt?>
:::

### Examples

**Example ($x' = x$ and the exponential).** Let $E = \mathbb{R}$, $v(t, x) = x$, $t_0 = 0$ and $x = 1$. Start with the constant curve $\alpha_0 = 1$. Then
$$\alpha_1(t) = 1 + \int_0^t 1\,d\tau = 1 + t, \qquad \alpha_2(t) = 1 + \int_0^t (1 + \tau)\,d\tau = 1 + t + \frac{t^2}{2},$$
and by induction $\alpha_n(t) = \sum_{k=0}^n t^k/k!$, because $\int_0^t \tau^k/k!\,d\tau = t^{k+1}/(k+1)!$. The Picard iterates are the partial sums of $e^t$, and the fixed point is $e^t$. Condition 4 with $L = 1 + a$ asks $h \le a/(1 + a) < 1$, although $e^t$ exists for all $t$.

**Example ($x' = x^2$ and a finite time of existence).** Let $v(t, x) = x^2$, $t_0 = 0$, $x = x_0 = 1$, $r = 0$. On $\bar B(1, a) = [1 - a, 1 + a]$ the bound is $L = (1 + a)^2$, and $|x^2 - y^2| = |x + y||x - y| \le 2(1 + a)|x - y|$, so $K = 2(1 + a)$. Condition 4 asks $h \le a/(1 + a)^2$. The best choice is $a = 1$, with $h = 1/4$. The exact solution $x(t) = 1/(1 - t)$ tends to $\infty$ as $t \to 1^-$, so no theorem gives a solution on $[0, 1]$: existence is local in an essential way.

**Counterexample (Completeness and finite dimension).** Continuity of $v$ without a Lipschitz condition gives existence in $\mathbb{R}^n$ (Peano's theorem), but not in a general Banach space. Let $E = c_0$, the space of real sequences that tend to $0$ with the supremum norm, and let $v(x)_n = \sqrt{|x_n|} + \frac{1}{n + 1}$. It maps $c_0$ to $c_0$ and is continuous, because $|\sqrt{|s|} - \sqrt{|u|}| \le \sqrt{|s - u|}$ gives $\|v(x) - v(y)\| \le \sqrt{\|x - y\|}$. Suppose that $\alpha$ is a solution with $\alpha(0) = 0$ on $[0, \varepsilon)$. Each coordinate satisfies $\alpha_n' > 0$, so $\alpha_n(t) > 0$ for $t > 0$, and $\frac{d}{dt} 2\sqrt{\alpha_n} = \alpha_n'/\sqrt{\alpha_n} > 1$. Integration from $s > 0$ and $s \to 0$ give $\alpha_n(t) \ge t^2/4$ for each $n$. Then $\alpha(t) \notin c_0$ for $t > 0$, a contradiction.

### The library around it

`Mathlib.Analysis.ODE.PicardLindelof` defines `IsPicardLindelof`, `ODE.picard` and `ODE.FunSpace` and proves the estimates on the iterates; `Mathlib.Analysis.ODE.ExistUnique` states the existence theorems and the uniqueness theorems of Section 1. In the names, the suffix `₀` is the case $x = x_0$ and `_lipschitzOnWith` adds the dependence on the initial value. `IsPicardLindelof.of_time_independent` and `IsPicardLindelof.of_contDiffAt_one` produce the hypotheses for an autonomous field. By `ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt`, a solution of an equation with a $C^n$ field is $C^n$.

Common errors of a learner:

- Forgetting condition 4. The field `mul_max_le` of the structure is $L h \le a - r$, and an instance must check it.
- Forgetting `CompleteSpace E`, which the integral and the fixed point need.

### Exercises

1. (A) Compute the first three Picard iterates for $x' = 2tx$, $x(0) = 1$, starting from $\alpha_0 = 1$. Guess the solution and check it.
2. (A) For $v(t, x) = \cos x$ on $\mathbb{R}$, give constants $a, r, L, K$ such that the Picard-Lindelöf conditions hold on $[-h, h]$ for every $h$. Conclude that the solution exists on $\mathbb{R}$.
3. (B) Show that $x' = 1 + x^2$, $x(0) = 0$ has the solution $\tan t$, and compute the interval $h$ that the theorem gives for the best choice of $a$. Compare with $\pi/2$.
4. (B) Let $v$ be continuous on $\mathbb{R} \times \mathbb{R}^n$, $K$-Lipschitz in $x$ on all of $\mathbb{R}^n$. Show with the weighted metric $\sup_t e^{-2K|t - t_0|}\|\alpha(t) - \beta(t)\|$ that the Picard map is a contraction on the continuous curves on $[t_0 - T, t_0 + T]$ for every $T$, so that the solution is global.
5. (C) Let $f : E \to E$ be $C^1$ on a Banach space and let $\varphi_t(x)$ be the solution with $\varphi_0(x) = x$, where it exists. Show that $\varphi_{s+t} = \varphi_s \circ \varphi_t$ where both sides are defined. Hint: both sides solve the same initial value problem in $s$.

### Notes and history

Cauchy proved the existence of solutions by a polygon method for fields with a continuous derivative, and Lipschitz replaced this hypothesis by the condition that now has his name. Picard introduced the method of successive approximations in 1890, and Lindelöf gave the theorem its modern form with the Lipschitz condition in 1894. Peano proved existence for a continuous field in $\mathbb{R}^n$. That Peano's theorem fails in infinite dimension is due to Dieudonné, with an example in $c_0$ of the kind given above. The iterates $T^n$ avoid the shrinking of the interval that a direct contraction argument needs.

### Reference

<?reference?>
