---
title: The Poisson integral
kind: theory
modules:
  - Mathlib.Analysis.Complex.Poisson
  - Mathlib.Analysis.Complex.Harmonic.Poisson
  - Mathlib.Analysis.Complex.BorelCaratheodory
explains:
  E3: [poissonKernel, herglotzRieszKernel, DiffContOnCl.circleAverage_poissonKernel_smul, InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul, le_re_herglotzRieszKernel, Complex.borelCaratheodory]
  E2: [poissonKernel_def, herglotzRieszKernel_def, poissonKernel_eq_re_herglotzRieszKernel, re_herglotzRieszKernel_le, DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul, InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul, analyticOnNhd_circleAverage_herglotzRieszKernel_smul, re_circleAverage_herglotzRieszKernel_smul, continuousOn_poissonKernel_sphere, poissonKernel_add_const, Complex.borelCaratheodory_zero]
  E1: auto
families: []
requires: [V19.C02, V19.C03, V19.C04, V18.C08]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Poisson integral

### Overview

The mean value property of Section 1 of this chapter gives the value of a harmonic function at the centre of a disc from its values on the boundary circle. The Poisson integral gives the value at every point $w$ of the disc, as an average with a positive weight, the Poisson kernel. This section proves the Poisson formula for holomorphic and for harmonic functions, the Harnack bounds, and the holomorphy of the Herglotz-Riesz integral. It ends with the Borel-Caratheodory inequality, which bounds $|f|$ by an upper bound of $\operatorname{Re} f$.

### Definitions

**Definition (Poisson kernel).** For $c, w, z \in \mathbb{C}$ with $z \ne w$,
$$P(c, w, z) = \frac{|z - c|^2 - |w - c|^2}{|z - w|^2}.$$

**Definition (Herglotz-Riesz kernel).** For $z \ne w$,
$$H(c, w, z) = \frac{(z - c) + (w - c)}{(z - c) - (w - c)}.$$

Here $z$ runs on the circle $|z - c| = R$ and $w$ is in the open disc. For $c = 0$, $w = re^{i\varphi}$ and $z = Re^{i\theta}$,
$$P(0, w, z) = \frac{R^2 - r^2}{R^2 - 2Rr\cos(\theta - \varphi) + r^2},$$
the classical form of the kernel.

### Theorems and proofs

**Theorem (Kernels).** $P(c, w, z) = \operatorname{Re} H(c, w, z)$ for $z \ne w$. For $|z - c| = R$ and $|w - c| < R$,
$$\frac{R - |w - c|}{R + |w - c|} \le P(c, w, z) \le \frac{R + |w - c|}{R - |w - c|}.$$
In particular $P > 0$ there.

*Proof.* Both kernels depend only on $z - c$ and $w - c$, so take $c = 0$. Multiply the numerator and the denominator of $H$ by $\overline{z - w}$:
$$H = \frac{(z + w)(\bar z - \bar w)}{|z - w|^2} = \frac{|z|^2 - |w|^2 + (w\bar z - z\bar w)}{|z - w|^2}.$$
The number $w\bar z - z\bar w = w\bar z - \overline{w \bar z}$ is purely imaginary, so $\operatorname{Re} H = P$. For the bounds, $|z| = R$ gives $R - |w| \le |z - w| \le R + |w|$, and $R^2 - |w|^2 = (R - |w|)(R + |w|)$. Divide. $\square$

::: mathlib
`poissonKernel` · `Mathlib.Analysis.Complex.Poisson`

`poissonKernel c w z : ℝ` and `herglotzRieszKernel c w z : ℂ` are total functions, unfolded by `poissonKernel_def` and `herglotzRieszKernel_def`. At `z = w` the division by `0` gives `0`. So `poissonKernel_eq_re_herglotzRieszKernel : poissonKernel c w = re ∘ herglotzRieszKernel c w` needs no hypothesis.

<?decl poissonKernel?>
<?decl herglotzRieszKernel?>
:::

::: mathlib
`le_re_herglotzRieszKernel` · `Mathlib.Analysis.Complex.Poisson`

This is the lower bound, for `z ∈ sphere c R` and `w ∈ ball c R`, and `re_herglotzRieszKernel_le` is the upper bound. `continuousOn_poissonKernel_sphere` gives continuity in `z` on the circle.

<?decl le_re_herglotzRieszKernel?>
:::

**Theorem (Poisson formula, holomorphic case).** Let $f$ be holomorphic on $B(c, R)$ and continuous on $\overline{B}(c, R)$, with values in a complex Banach space, and let $|w - c| < R$. Then
$$f(w) = \frac{1}{2\pi} \int_0^{2\pi} P(c, w, c + Re^{i\theta})\, f(c + Re^{i\theta})\, d\theta.$$

*Proof.* Take $c = 0$ by a translation. On the circle $z = Re^{i\theta}$, $dz = iz\, d\theta$, so for any continuous $g$ on the circle,
$$\frac{1}{2\pi i} \oint \frac{g(z)}{z - a}\, dz = \frac{1}{2\pi} \int_0^{2\pi} \frac{z}{z - a}\, g(z)\, d\theta. \tag{1}$$

Step 1: by the Cauchy integral formula of Chapter 2, Section 3, in its form with continuous boundary values, (1) with $g = f$ and $a = w$ is $f(w)$.

Step 2: let $w \ne 0$ and $w^* = R^2/\bar w$. Then $|w^*| = R^2/|w| > R$, so $z \mapsto f(z)/(z - w^*)$ is holomorphic on the open disc and continuous on the closed disc. By the Cauchy-Goursat theorem of Chapter 2, Section 2, (1) with $a = w^*$ is $0$.

Step 3: on the circle, $R^2 = z\bar z$, so
$$\frac{z}{z - w^*} = \frac{z\bar w}{z\bar w - z\bar z} = \frac{\bar w}{\bar w - \bar z} = -\frac{\bar w}{\bar z - \bar w}.$$

Step 4: subtract Step 2 from Step 1. The weight is
$$\frac{z}{z - w} + \frac{\bar w}{\bar z - \bar w} = \frac{z(\bar z - \bar w) + \bar w(z - w)}{|z - w|^2} = \frac{|z|^2 - |w|^2}{|z - w|^2} = P(0, w, z).$$
For $w = 0$, $P = 1$ and the claim is the mean value property. $\square$

::: mathlib
`DiffContOnCl.circleAverage_poissonKernel_smul` · `Mathlib.Analysis.Complex.Poisson`

The statement is `DiffContOnCl ℂ f (ball c R) → w ∈ ball c R → circleAverage (poissonKernel c w • f) c R = f w`. The form with the real part of the Herglotz-Riesz kernel is `DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul`.

<?decl DiffContOnCl.circleAverage_poissonKernel_smul?>
:::

**Theorem (Poisson formula, harmonic case).** Let $u : \mathbb{C} \to \mathbb{R}$ be harmonic on $\overline{B}(c, R)$ and $|w - c| < R$. Then
$$u(w) = \frac{1}{2\pi} \int_0^{2\pi} P(c, w, c + Re^{i\theta})\, u(c + Re^{i\theta})\, d\theta.$$

*Proof.* As in the proof of the mean value property in Section 1, $u$ is harmonic on some $B(c, R')$ with $R' > R$, and $u = \operatorname{Re} F$ there with $F$ holomorphic. Apply the holomorphic case to $F$. The kernel is real, so the real part of the average of $P F$ is the average of $P u$. $\square$

::: mathlib
`InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul` · `Mathlib.Analysis.Complex.Harmonic.Poisson`

The hypothesis is `HarmonicOnNhd f (closedBall c R)`. The version for a function harmonic inside and continuous up to the boundary is `InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul`.

<?decl InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul?>
:::

**Theorem (Harnack inequality).** Let $u \ge 0$ be harmonic on $\overline{B}(c, R)$ and $|w - c| = r < R$. Then
$$\frac{R - r}{R + r}\, u(c) \le u(w) \le \frac{R + r}{R - r}\, u(c).$$

*Proof.* In the Poisson formula, $u \ge 0$ on the circle, so the bounds of the kernel theorem multiply the integrand by numbers between $(R - r)/(R + r)$ and $(R + r)/(R - r)$. The average of $u$ on the circle is $u(c)$ by the mean value property. $\square$

**Theorem (Herglotz-Riesz integral).** Let $g$ be continuous on the circle $|z| = R$ and define, for $|w| \ne R$,
$$G(w) = \frac{1}{2\pi} \int_0^{2\pi} H(0, w, Re^{i\theta})\, g(Re^{i\theta})\, d\theta.$$
Then $G$ is holomorphic off the circle. If $g$ is real, $\operatorname{Re} G$ is the Poisson integral of $g$, and it is harmonic in the disc.

*Proof.* For fixed $z$, $H(0, w, z) = (z + w)/(z - w)$ is holomorphic in $w \ne z$. Fix $w_0$ with $|w_0| \ne R$, and let $d > 0$ be its distance to the circle. For $|w - w_0| < d/2$ and $|z| = R$, $|z - w| > d/2$. There the $w$ derivative $2z/(z - w)^2$ of the integrand is bounded by $8R/d^2$, so differentiation under the integral sign (Volume 18, dominated convergence) gives a complex derivative. For real $g$, the real part commutes with the integral, and $\operatorname{Re} H = P$. The real part of a holomorphic function is harmonic by Section 1. $\square$

This harmonic function tends to $g(z_0)$ as $w \to z_0$ on the circle (Exercise 6), which solves the Dirichlet problem on the disc. The index of this edition has no declaration for this boundary limit.

::: mathlib
`analyticOnNhd_circleAverage_herglotzRieszKernel_smul` · `Mathlib.Analysis.Complex.Poisson`

For a circle integrable `f`, the average of `herglotzRieszKernel 0 w • f` is analytic in `w` on `(sphere 0 |R|)ᶜ`. `re_circleAverage_herglotzRieszKernel_smul` takes the real part inside the average.

<?decl analyticOnNhd_circleAverage_herglotzRieszKernel_smul?>
:::

**Theorem (Borel-Caratheodory).** Let $f$ be holomorphic on $B(0, R)$ with $\operatorname{Re} f \le M$ there, $M > 0$. Then for $|z| < R$,
$$|f(z)| \le \frac{2M|z|}{R - |z|} + |f(0)|\, \frac{R + |z|}{R - |z|}.$$

*Proof.* Step 1, the case $f(0) = 0$. Put $g = f/(2M - f)$. The denominator is not $0$, since $\operatorname{Re}(2M - f) \ge M > 0$. Also $|2M - f|^2 - |f|^2 = 4M^2 - 4M\operatorname{Re} f \ge 0$, so $|g| \le 1$, and $g(0) = 0$. The Schwarz lemma of Chapter 3, Section 2, scaled to the disc of radius $R$, gives $|g(z)| \le |z|/R$. Solve for $f$: $f = 2Mg/(1 + g)$, so
$$|f(z)| \le \frac{2M|g(z)|}{1 - |g(z)|} \le \frac{2M|z|/R}{1 - |z|/R} = \frac{2M|z|}{R - |z|}.$$

Step 2, the general case. The function $f - f(0)$ vanishes at $0$ and has real part at most $M + |f(0)|$. Step 1 gives $|f(z) - f(0)| \le 2(M + |f(0)|)|z|/(R - |z|)$. Add $|f(0)|$ and use $1 + 2|z|/(R - |z|) = (R + |z|)/(R - |z|)$. $\square$

::: mathlib
`Complex.borelCaratheodory` · `Mathlib.Analysis.Complex.BorelCaratheodory`

The bound on the real part is `MapsTo f (ball 0 R) {z | z.re ≤ M}`. Step 1 is `Complex.borelCaratheodory_zero`, with the extra hypothesis `f 0 = 0`.

<?decl Complex.borelCaratheodory?>
:::

### Examples

**Example (The kernel at a point).** Take $R = 1$, $c = 0$, $w = 1/2$. At $z = 1$, $P = (1 - 1/4)/(1/4) = 3$. At $z = -1$, $P = (3/4)/(9/4) = 1/3$. These are the two Harnack bounds, attained at the nearest and the farthest point.

**Example (Borel-Caratheodory is sharp).** Let $f(z) = 2Mz/(R - z)$ on $B(0, R)$. The map $z \mapsto z/(R - z)$ sends the disc onto the half plane $\operatorname{Re} > -1/2$, so $\operatorname{Re} f > -M$, and $\operatorname{Re}(-f) < M$. For $-f$, with $f(0) = 0$, the bound is $2M|z|/(R - |z|)$, which is attained at real $z > 0$.

### The library around it

The Poisson kernel moves with translations (`poissonKernel_add_const`). The file `Mathlib.Analysis.Complex.JensenFormula` uses `poissonKernel` for the Poisson-Jensen formula of Chapter 4, Section 2.

Common errors of a learner:

- Using the bounds of the kernel with `w` on the circle. They need `w ∈ ball c R`.
- Applying the Poisson formula for a function harmonic only on the open disc, with no continuity up to the boundary.

### Exercises

1. (A) Check from the formula that $P(0, w, Re^{i\theta}) = \sum_{n \in \mathbb{Z}} (r/R)^{|n|} e^{in(\theta - \varphi)}$ for $w = re^{i\varphi}$. Hint: expand $(z + w)/(z - w)$ in powers of $w/z$.
2. (A) Compute the Poisson integral of $g(e^{i\theta}) = \cos 2\theta$ on the unit circle.
3. (B) Use the Harnack inequality to show that an increasing sequence of harmonic functions on a connected open set that is bounded at one point converges locally uniformly. Hint: apply Harnack to $u_m - u_n$.
4. (B) Show that a positive harmonic function on $\mathbb{C}$ is constant, using Harnack with $R \to \infty$.
5. (B) Let $f$ be entire with $\operatorname{Re} f(z) \le A + B|z|^n$. Show that $f$ is a polynomial of degree at most $n$. Hint: Borel-Caratheodory with $R = 2|z|$, then Cauchy estimates.
6. (C) Prove that the Poisson integral $u$ of a continuous $g$ on the unit circle satisfies $u(w) \to g(z_0)$ as $w \to z_0$. Hint: split the circle into an arc near $z_0$ and its complement, and use that $P \to 0$ uniformly on the complement.

### Notes and history

The kernel carries the name of Poisson, and the inequality the name of Harnack. The Borel-Caratheodory inequality passes from bounds on the real part to bounds on the modulus in the theory of entire functions.

### Reference

<?reference?>
