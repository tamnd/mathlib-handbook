---
title: Maximum modulus, open mapping and the Schwarz lemma
kind: theory
modules:
  - Mathlib.Analysis.Complex.AbsMax
  - Mathlib.Analysis.Complex.OpenMapping
  - Mathlib.Analysis.Complex.Schwarz
explains:
  E3: [Complex.eqOn_of_isPreconnected_of_isMaxOn_norm, Complex.norm_le_of_forall_mem_frontier_norm_le, DiffContOnCl.ball_subset_image_closedBall, AnalyticOnNhd.is_constant_or_isOpen, Complex.norm_le_norm_of_mapsTo_ball]
  E2: [Complex.norm_eqOn_closedBall_of_isMaxOn, Complex.eqOn_closedBall_of_isMaxOn_norm, Complex.norm_eventually_eq_of_isLocalMax, Complex.eventually_eq_of_isLocalMax_norm, Complex.norm_eqOn_of_isPreconnected_of_isMaxOn, Complex.exists_mem_frontier_isMaxOn_norm, Complex.eqOn_of_eqOn_frontier, Complex.eqOn_closure_of_eqOn_frontier, Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm, AnalyticAt.eventually_constant_or_nhds_le_map_nhds, AnalyticOnNhd.is_constant_or_isOpenMap, Polynomial.isOpenQuotientMap_eval, Complex.isOpenQuotientMap_pow, Complex.norm_deriv_le_one_of_mapsTo_ball, Complex.norm_deriv_le_div_of_mapsTo_ball, Complex.dist_le_div_mul_dist_of_mapsTo_ball, Complex.norm_dslope_le_div_of_mapsTo_ball, Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div]
  E1: auto
families: []
requires: [V19.C01, V19.C02, V17.C07, V13]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Maximum modulus, open mapping and the Schwarz lemma

### Overview

The Cauchy formula at the centre of a circle says that $f(c)$ is the average of $f$ over the circle. An average cannot be larger in modulus than all the values it averages, unless they all agree. This gives the maximum modulus principle: a nonconstant holomorphic function on a connected open set has no maximum of $|f|$ inside. From it, this section derives the open mapping theorem and the Schwarz lemma, which bounds a holomorphic self-map of the disc that fixes $0$.

The section uses Chapter 2, Section 3, the identity theorem of Volume 17, Chapter 7, and connectedness from Volume 13.

### Definitions

A *domain* is a connected open subset of $\mathbb{C}$. For a function $f$ on a set $S$, $|f|$ *has a maximum on $S$ at* $c \in S$ if $|f(z)| \le |f(c)|$ for all $z \in S$. It has a *local maximum* at $c$ if this holds on some neighbourhood of $c$.

**Definition (Slope function).** For $f$ differentiable at $c$, the *slope function* is $s_c f(z) = (f(z) - f(c))/(z - c)$ for $z \ne c$ and $s_c f(c) = f'(c)$.

::: mathlib
`dslope` · `Mathlib.Analysis.Calculus.DSlope`

The slope function is `dslope f c`. Mathlib states a maximum of the norm as `IsMaxOn (norm ∘ f) s c` and a local maximum as `IsLocalMax (norm ∘ f) c`.

<?decl dslope?>
:::

### Theorems and proofs

**Lemma (Mean value property).** Let $f$ be holomorphic on a neighbourhood of $\bar D(c, r)$. Then
$$f(c) = \frac{1}{2\pi}\int_0^{2\pi} f(c + re^{i\theta})\,d\theta.$$

*Proof.* Take $w = c$ in the Cauchy formula. With $z = c + re^{i\theta}$, $dz = ire^{i\theta}d\theta$ and $z - c = re^{i\theta}$, so
$$f(c) = \frac{1}{2\pi i}\int_0^{2\pi} \frac{f(c + re^{i\theta})}{re^{i\theta}}\, ire^{i\theta}\,d\theta = \frac{1}{2\pi}\int_0^{2\pi} f(c + re^{i\theta})\,d\theta. \qquad \square$$

**Theorem (Local maximum modulus).** Let $f$ be holomorphic on $D(c, R)$, and let $|f|$ have a maximum on $D(c, R)$ at $c$. Then $f$ is constant on $D(c, R)$.

*Proof.* Put $M = |f(c)|$. If $M = 0$ then $f = 0$. Otherwise put $u = \overline{f(c)}/M$, so $|u| = 1$ and $uf(c) = M$. Fix $0 < r < R$ and write $\phi(\theta) = \operatorname{Re}(u f(c + re^{i\theta}))$. Then $\phi(\theta) \le |f(c + re^{i\theta})| \le M$. The lemma gives
$$M = \operatorname{Re}(u f(c)) = \frac{1}{2\pi}\int_0^{2\pi} \phi(\theta)\,d\theta.$$
So the continuous function $M - \phi \ge 0$ has integral $0$, and therefore $\phi = M$ everywhere. Then $u f(z)$ has real part $M$ and modulus at most $M$, so $u f(z) = M$ and $f(z) = f(c)$ for $|z - c| = r$. $\square$

**Theorem (Maximum modulus principle).** Let $U$ be a domain, $f$ holomorphic on $U$, and let $|f|$ have a maximum on $U$ at $c \in U$. Then $f$ is constant on $U$.

*Proof.* Let $S = \{z \in U : f(z) = f(c)\}$. It contains $c$, and it is closed in $U$ since $f$ is continuous. It is open: for $z \in S$, $|f(z)| = |f(c)|$ is the maximum of $|f|$ on $U$, so on a disc $D(z, \rho) \subseteq U$ the local theorem gives $f = f(z) = f(c)$. Since $U$ is connected, $S = U$. $\square$

**Corollary (Bounded domains).** Let $U$ be a bounded nonempty open set, and $f$ continuous on $\bar U$ and holomorphic on $U$. Then $|f|$ attains its maximum on $\bar U$ at a point of the frontier $\partial U$. So if $|f| \le C$ on $\partial U$, then $|f| \le C$ on $\bar U$.

*Proof.* $\bar U$ is closed and bounded, hence compact (Chapter 1, Section 1), so $|f|$ attains its maximum at some $z_0 \in \bar U$. If $z_0 \in \partial U$, the claim holds. Otherwise $z_0 \in U$. Let $V$ be the connected component of $U$ that contains $z_0$; it is open. By the principle, $f = f(z_0)$ on $V$, hence on $\bar V$. The set $V$ is nonempty, open and bounded, so $V \ne \mathbb{C}$. Since $\mathbb{C}$ is connected, $V$ is not closed, and there is a point $p \in \bar V \setminus V$. This $p$ is not in $U$: otherwise its component would be an open set that meets $V$, hence equal to $V$. So $p \in \partial U$, and $|f(p)| = |f(z_0)|$ is the maximum. $\square$

::: mathlib
`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` · `Mathlib.Analysis.Complex.AbsMax`

The statement takes `IsPreconnected U`, `IsOpen U`, `DifferentiableOn ℂ f U`, `c ∈ U` and `IsMaxOn (norm ∘ f) U c`, and concludes `EqOn f (const E (f c)) U`. The values may lie in any complex normed space `F` with `[StrictConvexSpace ℝ F]`. Without it only the norm is constant: `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn`. The local forms are `Complex.eqOn_closedBall_of_isMaxOn_norm` and `Complex.eventually_eq_of_isLocalMax_norm`.

<?decl Complex.eqOn_of_isPreconnected_of_isMaxOn_norm?>
:::

::: mathlib
`Complex.norm_le_of_forall_mem_frontier_norm_le` · `Mathlib.Analysis.Complex.AbsMax`

For a bounded `U` and `DiffContOnCl ℂ f U`, a bound `‖f z‖ ≤ C` on `frontier U` gives `‖f z‖ ≤ C` on `closure U`. The point of the frontier is `Complex.exists_mem_frontier_isMaxOn_norm`, which needs `[FiniteDimensional ℂ E]` for compactness. Uniqueness from the frontier is `Complex.eqOn_closure_of_eqOn_frontier`.

<?decl Complex.norm_le_of_forall_mem_frontier_norm_le?>
:::

**Theorem (Open mapping).** Let $U$ be a domain and $f$ holomorphic and nonconstant on $U$. Then $f(V)$ is open for every open $V \subseteq U$.

*Proof.* Let $z_0 \in V$. By the identity theorem (Volume 17, Chapter 7), $f - f(z_0)$ does not vanish on any neighbourhood of $z_0$, since otherwise $f$ would be constant on $U$. By the isolated zeros, there is $r > 0$ with $\bar D(z_0, r) \subseteq V$ and $f(z) \ne f(z_0)$ for $0 < |z - z_0| \le r$. The circle is compact, so $\varepsilon = \min_{|z - z_0| = r}|f(z) - f(z_0)| > 0$.

Let $|w - f(z_0)| < \varepsilon/2$. On the circle, $|f(z) - w| \ge \varepsilon - \varepsilon/2 > |f(z_0) - w|$. Suppose that $f - w$ has no zero on $\bar D(z_0, r)$. Then $g = 1/(f - w)$ is holomorphic on a neighbourhood of the closed disc. The maximum of $|g|$ on the compact closed disc is not attained on the circle, because $|g(z_0)|$ is larger than every value there. So it is attained at an interior point $z_1$, and the local theorem makes $g$, hence $f$, constant near $z_1$. By the identity theorem $f$ is constant on $U$, a contradiction. So $w = f(z)$ for some $z \in \bar D(z_0, r) \subseteq V$. $\square$

::: mathlib
`DiffContOnCl.ball_subset_image_closedBall` · `Mathlib.Analysis.Complex.OpenMapping`

The statement takes `DiffContOnCl ℂ f (ball z₀ r)`, `0 < r`, `∀ z ∈ sphere z₀ r, ε ≤ ‖f z - f z₀‖` and `∃ᶠ z in 𝓝 z₀, f z ≠ f z₀`, and concludes `ball (f z₀) (ε / 2) ⊆ f '' closedBall z₀ r`.

<?decl DiffContOnCl.ball_subset_image_closedBall?>
:::

::: mathlib
`AnalyticOnNhd.is_constant_or_isOpen` · `Mathlib.Analysis.Complex.OpenMapping`

For `g : E → ℂ` with `AnalyticOnNhd ℂ g U` and `IsPreconnected U`, it gives `(∃ w, ∀ z ∈ U, g z = w) ∨ ∀ s ⊆ U, IsOpen s → IsOpen (g '' s)`. The pointwise form is `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`. For polynomials, `Polynomial.isOpenQuotientMap_eval` gives an open quotient map when the degree is not zero.

<?decl AnalyticOnNhd.is_constant_or_isOpen?>
:::

**Theorem (Schwarz lemma).** Let $f$ be holomorphic on the unit disc $\mathbb{D}$, with $|f| \le 1$ and $f(0) = 0$. Then $|f(z)| \le |z|$ for $z \in \mathbb{D}$, and $|f'(0)| \le 1$. If $|f(z_0)| = |z_0|$ for some $z_0 \ne 0$, or $|f'(0)| = 1$, then $f(z) = az$ with $|a| = 1$.

*Proof.* By Chapter 2, Section 3, $f(z) = \sum_{n \ge 1} a_n z^n$ on all of $\mathbb{D}$, since $a_0 = f(0) = 0$. So $g(z) = \sum_{n \ge 1} a_n z^{n-1}$ converges on $\mathbb{D}$ and is holomorphic there. It equals $f(z)/z$ for $z \ne 0$ and $f'(0)$ at $0$: it is the slope function $s_0 f$. Fix $z \in \mathbb{D}$ and $|z| < r < 1$. On the circle $|\zeta| = r$, $|g(\zeta)| \le 1/r$. By the corollary on the disc $D(0, r)$, $|g(z)| \le 1/r$. Let $r \to 1$: $|g(z)| \le 1$. This gives $|f(z)| \le |z|$ and $|f'(0)| = |g(0)| \le 1$. In the case of equality, $|g|$ attains its maximum $1$ on $\mathbb{D}$ at an interior point. By the principle, $g = a$ is constant with $|a| = 1$, and $f(z) = az$. $\square$

Scaling gives the general form. If $f$ is holomorphic on $D(c, R_1)$ with values in $\bar D(f(c), R_2)$, then $|f(z) - f(c)| \le (R_2/R_1)|z - c|$ and $|f'(c)| \le R_2/R_1$.

::: mathlib
`Complex.norm_le_norm_of_mapsTo_ball` · `Mathlib.Analysis.Complex.Schwarz`

The statement takes `DifferentiableOn ℂ f (ball 0 R)`, `MapsTo f (ball 0 R) (closedBall 0 R)`, `f 0 = 0` and `‖z‖ < R`, and concludes `‖f z‖ ≤ ‖z‖`. The general form is `Complex.dist_le_div_mul_dist_of_mapsTo_ball`. The derivative bounds are `Complex.norm_deriv_le_div_of_mapsTo_ball` and `Complex.norm_deriv_le_one_of_mapsTo_ball`. The case of equality is `Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`, which needs a strictly convex target.

<?decl Complex.norm_le_norm_of_mapsTo_ball?>
:::

### Examples

**Example.** On $\bar D(0, 1)$, $|e^z| = e^{\operatorname{Re} z}$ has its maximum $e$ at $z = 1$, on the boundary. Its minimum $e^{-1}$ is at $z = -1$, also on the boundary, as Exercise 1 predicts.

**Example.** For $|a| < 1$, the map $\varphi_a(z) = (z - a)/(1 - \bar a z)$ sends $\mathbb{D}$ into $\mathbb{D}$. On $|z| = 1$, $|1 - \bar a z| = |\bar z - \bar a| = |z - a|$, so $|\varphi_a| = 1$ there. By the corollary, $|\varphi_a| \le 1$ on $\bar{\mathbb{D}}$, and by the principle $|\varphi_a| < 1$ inside.

### The library around it

Common errors of a learner:

- Applying the maximum principle on a set that is not connected. On $D(0,1) \cup D(3, 1)$ the function equal to $0$ and $1$ on the two discs is holomorphic and attains $\max|f|$ inside.
- Forgetting the strict convexity of the target in the forms that conclude `f = const`.
- Expecting a maximum on the frontier of an unbounded set. On the strip $|\operatorname{Im} z| < \pi/2$ the function $\exp(\exp z)$ is bounded on the frontier but not inside.

### Exercises

1. (A) Show that a nonconstant holomorphic function on a domain $U$ with no zeros has no minimum of $|f|$ in $U$. Hint: apply the principle to $1/f$.
2. (B) Let $f$ be holomorphic on a domain $U$ with $\operatorname{Re} f$ having a maximum in $U$. Show that $f$ is constant. Hint: $e^f$.
3. (B) Let $f : \mathbb{D} \to \mathbb{D}$ be holomorphic with $f(1/2) = 0$. Show that $|f'(1/2)| \le 4/3$. Hint: compose with $\varphi_{-1/2}$ from the last example.
4. (B) Show that a holomorphic bijection $f : \mathbb{D} \to \mathbb{D}$ with $f(0) = 0$ is a rotation. Hint: apply Schwarz to $f$ and $f^{-1}$.
5. (B) Show that a nonconstant polynomial maps $\mathbb{C}$ onto $\mathbb{C}$. Hint: the image is open, and closed since $|p(z)| \to \infty$.
6. (C) Let $f$ be holomorphic on $\mathbb{D}$ with $|f| \le 1$. Prove the Schwarz-Pick inequality $\left|\frac{f(z) - f(w)}{1 - \overline{f(w)}f(z)}\right| \le \left|\frac{z - w}{1 - \bar w z}\right|$.

### Notes and history

The lemma is named after Schwarz. Carathéodory gave its modern proof by the maximum principle, and Pick extended it to the invariant form of Exercise 6.

### Reference

<?reference?>
