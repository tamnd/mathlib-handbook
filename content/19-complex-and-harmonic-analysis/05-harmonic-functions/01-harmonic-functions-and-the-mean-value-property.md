---
title: Harmonic functions and the mean value property
kind: theory
modules:
  - Mathlib.Analysis.Complex.Harmonic.Analytic
  - Mathlib.Analysis.Complex.Harmonic.MeanValue
  - Mathlib.Analysis.Complex.Harmonic.Liouville
  - Mathlib.Analysis.Complex.MeanValue
explains:
  E3: [InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq, HarmonicAt.analyticAt, InnerProductSpace.HarmonicOnNhd.circleAverage_eq, InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant, DiffContOnCl.circleAverage]
  E2: [HarmonicAt.analyticAt_complex_partial, HarmonicAt.differentiableAt_complex_partial, InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq, InnerProductSpace.HarmonicContOnCl.circleAverage_eq, DiffContOnCl.circleAverage_smul_div, circleAverage_of_differentiable_on_off_countable]
  E1: auto
families: []
requires: [V19.C02, V19.C04, V16.C06, V17.C04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Harmonic functions and the mean value property

### Overview

The solutions of the Laplace equation $u_{xx} + u_{yy} = 0$ are the harmonic functions. In two variables they are tied to holomorphic functions: the real part of a holomorphic function is harmonic, and on a disc every harmonic function is such a real part. This section proves both directions and deduces three properties of harmonic functions from complex analysis: they are real analytic, the value at the centre of a disc is the average on the boundary circle, and a bounded harmonic function on $\mathbb{C}$ is constant. It also proves the maximum principle from the mean value property.

### Definitions

Write $z = x + iy$ and identify $\mathbb{C}$ with the Euclidean plane $\mathbb{R}^2$.

**Definition (Harmonic function).** Let $F$ be a real normed space. A function $u : \mathbb{C} \to F$ is harmonic at $z_0$ when it is $C^2$ in the real sense on a neighbourhood of $z_0$ and its Laplacian $\Delta u = u_{xx} + u_{yy}$ vanishes on a neighbourhood of $z_0$. It is harmonic on a set $S$ when it is harmonic at each point of $S$.

**Definition (Circle average).** For $u : \mathbb{C} \to F$, $c \in \mathbb{C}$ and $R \in \mathbb{R}$, the circle average is
$$\operatorname{avg}_{c, R}\, u = \frac{1}{2\pi} \int_0^{2\pi} u(c + Re^{i\theta})\, d\theta.$$

::: mathlib
`InnerProductSpace.HarmonicAt` · `Mathlib.Analysis.InnerProductSpace.Harmonic.Basic`

`HarmonicAt f x`, for `f : E → F` on a finite dimensional real inner product space `E`, is `ContDiffAt ℝ 2 f x` with the Laplacian eventually `0` near `x`. `HarmonicOnNhd f s` asks it at every `x ∈ s`, and `HarmonicContOnCl f s` adds continuity on the closure. This chapter uses `E = ℂ`.

<?decl InnerProductSpace.HarmonicAt?>
:::

### Theorems and proofs

**Theorem (Real parts are harmonic).** Let $f = u + iv$ be holomorphic on an open set $U$. Then $u$ and $v$ are harmonic on $U$.

*Proof.* By Chapter 2, Section 3, $f$ is analytic, so $u$ and $v$ are $C^\infty$. The Cauchy-Riemann equations of Chapter 2, Section 1 give $u_x = v_y$ and $u_y = -v_x$. Differentiate the first in $x$ and the second in $y$: $u_{xx} = v_{yx}$ and $u_{yy} = -v_{xy}$. The mixed partials of a $C^2$ function agree (Volume 17, Chapter 4), so $u_{xx} + u_{yy} = 0$. The same works for $v$, the real part of $-if$. $\square$

**Theorem (Harmonic functions are real parts).** Let $u : \mathbb{C} \to \mathbb{R}$ be harmonic on a disc $B = B(c, R)$. Then there is $F$ holomorphic on $B$ with $\operatorname{Re} F = u$ on $B$.

*Proof.* Step 1: the function $g = u_x - i u_y$ is holomorphic on $B$. It is $C^1$ because $u$ is $C^2$. Its real part $p = u_x$ and imaginary part $q = -u_y$ satisfy
$$p_x = u_{xx} = -u_{yy} = q_y, \qquad p_y = u_{xy} = u_{yx} = -q_x,$$
by $\Delta u = 0$ and the symmetry of second derivatives. A $C^1$ function that satisfies the Cauchy-Riemann equations is holomorphic (Chapter 2, Section 1).

Step 2: a holomorphic function on a disc has a primitive (Chapter 2, Section 2). Let $F$ be the primitive of $g$ with $F(c) = u(c)$, and write $F = U + iV$.

Step 3: for a holomorphic function, $F' = U_x + iV_x = U_x - iU_y$ by the Cauchy-Riemann equations. So $F' = g$ gives $U_x = u_x$ and $U_y = u_y$. The difference $U - u$ has gradient $0$ on the connected set $B$, so it is constant, and it is $0$ at $c$. $\square$

The holomorphic function $F$ is unique up to an imaginary constant, and $V = \operatorname{Im} F$ is the harmonic conjugate of $u$.

**Corollary (Analyticity).** A harmonic function $u : \mathbb{C} \to \mathbb{R}$ is real analytic, and $u_x - iu_y$ is holomorphic.

*Proof.* Near a point $u = \operatorname{Re} F$ with $F$ holomorphic. The power series of $F$ at $c$ converges on a disc, and the real part of $\sum a_n (z - c)^n$ is a convergent power series in $x - \operatorname{Re} c$ and $y - \operatorname{Im} c$. The second claim is Step 1. $\square$

::: mathlib
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` · `Mathlib.Analysis.Complex.Harmonic.Analytic`

From `HarmonicOnNhd f (ball z R)` it gives an `F` with `AnalyticOnNhd ℂ F (ball z R)` and real part `f` there. The form for all of `ℂ` is `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`. Step 1 is `HarmonicAt.analyticAt_complex_partial` (and `HarmonicAt.differentiableAt_complex_partial`), with $u_x - i u_y$ written as `fderiv ℝ f z 1 - I * fderiv ℝ f z I`. The corollary is `HarmonicAt.analyticAt : AnalyticAt ℝ f x`.

<?decl InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq?>
<?decl HarmonicAt.analyticAt?>
:::

**Theorem (Mean value property).** Let $u : \mathbb{C} \to \mathbb{R}$ be harmonic on the closed disc $\overline{B}(c, R)$. Then $u(c) = \operatorname{avg}_{c, R}\, u$.

*Proof.* Step 1: the set where $u$ is harmonic is open and contains the compact set $\overline{B}(c, R)$, so it contains $B(c, R')$ for some $R' > R$. Step 2: by the previous theorem, $u = \operatorname{Re} F$ on $B(c, R')$ with $F$ holomorphic. Step 3: the Cauchy integral formula of Chapter 2, Section 3 on the circle $z = c + Re^{i\theta}$, with $dz = iRe^{i\theta}\, d\theta$, gives
$$F(c) = \frac{1}{2\pi i} \oint \frac{F(z)}{z - c}\, dz = \frac{1}{2\pi i} \int_0^{2\pi} \frac{F(c + Re^{i\theta})}{Re^{i\theta}}\, iRe^{i\theta}\, d\theta = \operatorname{avg}_{c, R}\, F.$$
Step 4: take real parts. The real part commutes with the integral, since it is a continuous real linear map. $\square$

Steps 3 and 4 also give the mean value property of a holomorphic $F$.

::: mathlib
`InnerProductSpace.HarmonicOnNhd.circleAverage_eq` · `Mathlib.Analysis.Complex.Harmonic.MeanValue`

The statement is `HarmonicOnNhd f (closedBall c |R|) → circleAverage f c R = f c`, for `f` with values in a real Banach space. `Real.circleAverage` takes any real `R`, hence the radius `|R|`. Under `HarmonicContOnCl f (ball c |R|)` the result is `InnerProductSpace.HarmonicContOnCl.circleAverage_eq`.

<?decl InnerProductSpace.HarmonicOnNhd.circleAverage_eq?>
:::

::: mathlib
`DiffContOnCl.circleAverage` · `Mathlib.Analysis.Complex.MeanValue`

The holomorphic case: `DiffContOnCl ℂ f (ball c |R|) → circleAverage f c R = f c`. `circleAverage_of_differentiable_on_off_countable` allows a countable exceptional set, and `DiffContOnCl.circleAverage_smul_div` is the Cauchy formula at an interior point.

<?decl DiffContOnCl.circleAverage?>
:::

**Theorem (Maximum principle).** Let $U \subseteq \mathbb{C}$ be open and connected, and let $u : \mathbb{C} \to \mathbb{R}$ be harmonic on $U$. If $u$ has a maximum on $U$ at a point of $U$, then $u$ is constant on $U$.

*Proof.* Let $M$ be the maximum and $S = \{z \in U : u(z) = M\}$. The set $S$ is not empty and is closed in $U$, since $u$ is continuous. It is open: let $c \in S$ and $\overline{B}(c, \rho) \subseteq U$. For $0 < r \le \rho$, the mean value property gives $\operatorname{avg}_{c, r}(M - u) = 0$. The function $\theta \mapsto M - u(c + re^{i\theta})$ is continuous and $\ge 0$, so its integral is $0$ only if it is $0$ everywhere. So $u = M$ on each circle of radius $r \le \rho$, hence on $\overline{B}(c, \rho)$. Since $U$ is connected, $S = U$. $\square$

The index of this edition has no declaration for the maximum principle of harmonic functions in this form.

**Theorem (Liouville for harmonic functions).** A harmonic function $u : \mathbb{C} \to \mathbb{R}$ that is bounded above is constant.

*Proof.* Step 1: by the theorem on real parts for the plane, $u = \operatorname{Re} F$ with $F$ entire. Step 2: the function $e^{F}$ is entire, and $|e^{F}| = e^{u} \le e^{M}$ when $u \le M$. Step 3: by Liouville's theorem (Chapter 3, Section 1), $e^F$ is a constant $a \ne 0$. Step 4: then $F' e^F = 0$, so $F' = 0$, and $F$ is constant on the connected plane. So $u$ is constant. $\square$

::: mathlib
`InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant` · `Mathlib.Analysis.Complex.Harmonic.Liouville`

The statement is `HarmonicOnNhd f univ → IsBounded (range f) → ∀ z w, f z = f w`. It asks a bound on the norm, not a bound above, since `f` takes values in a normed space.

<?decl InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant?>
:::

### Examples

**Example (Polynomials).** The function $u = x^2 - y^2 = \operatorname{Re}(z^2)$ is harmonic. Its Step 1 function is $u_x - iu_y = 2x + 2iy = 2z$, with primitive $z^2$. The function $x^2 + y^2$ is not harmonic: its Laplacian is $4$. The mean value property fails for it at $0$: the average on $|z| = R$ is $R^2 \ne 0$.

**Example (The logarithm).** The function $u(z) = \log|z|$ is harmonic on $\mathbb{C} \setminus \{0\}$: near each point it is the real part of a branch of $\log z$. On the annulus there is no global $F$ with $\operatorname{Re} F = u$. Such an $F$ would have $F' = u_x - iu_y = 1/z$ on the annulus, and $\oint dz/z = 2\pi i \ne 0$ on $|z| = 1$, while the circle integral of a derivative is $0$. So the theorem on real parts needs the disc, or at least a simply connected set.

### The library around it

The files of this section are the two dimensional part of `Mathlib.Analysis.InnerProductSpace.Harmonic`. `AnalyticAt.harmonicAt_log_norm` makes $\log\|f\|$ harmonic for a holomorphic $f$ without zeros.

Common errors of a learner:

- Applying the mean value theorem with `HarmonicOnNhd f (ball c R)`. It needs the closed disc, or `HarmonicContOnCl` on the open disc.
- Expecting a harmonic conjugate on any open set. On the annulus $\log|z|$ has none.
- Writing the circle average with radius `R` and forgetting `|R|` in the hypothesis.

### Exercises

1. (A) Show that $e^x \sin y$ and $x^3 - 3xy^2$ are harmonic, and find holomorphic functions with these real parts.
2. (A) Show that the product of two harmonic functions need not be harmonic. Hint: try $x \cdot x$.
3. (B) Let $u$ be harmonic on $\mathbb{C}$ and $u(z) \ge 0$ for all $z$. Show that $u$ is constant.
4. (B) Prove the minimum principle, and deduce that a harmonic function on a bounded open set that is continuous up to the boundary takes its maximum and minimum on the boundary.
5. (B) Show that if $u$ is harmonic and $f$ is holomorphic, then $u \circ f$ is harmonic. Hint: write $u = \operatorname{Re} F$ locally.
6. (C) Show that a continuous $u$ with the mean value property on every small circle is harmonic. Hint: use Section 2 to solve the Dirichlet problem on a small disc with the boundary values of $u$, and apply the maximum principle to the difference.
7. (C) Let $u$ be harmonic on $\mathbb{C}$ with $|u(z)| \le A + B|z|^n$. Show that $u$ is the real part of a polynomial of degree at most $n$. Hint: estimate the coefficients of $F$ from the Poisson integral of Section 2 or with the Borel-Caratheodory inequality.

### Notes and history

The equation $\Delta u = 0$ appears in the work of Laplace on gravitation in the late eighteenth century. The mean value property is due to Gauss for the potential of a mass distribution. In the plane, the link with holomorphic functions through the Cauchy-Riemann equations was the basis of Riemann's approach to function theory.

### Reference

<?reference?>
