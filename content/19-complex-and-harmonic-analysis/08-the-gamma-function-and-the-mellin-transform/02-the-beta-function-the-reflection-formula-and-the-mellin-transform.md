---
title: The beta function, the reflection formula and the Mellin transform
kind: theory
modules:
  - Mathlib.Analysis.SpecialFunctions.Gamma.Beta
  - Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
  - Mathlib.Analysis.MellinTransform
  - Mathlib.Analysis.MellinInversion
  - Mathlib.Analysis.PSeriesComplex
explains:
  E3: [Complex.betaIntegral, Complex.Gamma_mul_Gamma_eq_betaIntegral, Complex.GammaSeq_tendsto_Gamma, Complex.Gamma_mul_Gamma_one_sub, Complex.Gamma_ne_zero, Complex.Gamma_mul_Gamma_add_half, mellin, MellinConvergent, mellinConvergent_of_isBigO_rpow, mellinInv_mellin_eq]
  E2: [Complex.betaIntegral_convergent, Complex.betaIntegral_symm, Complex.GammaSeq, Complex.GammaSeq_eq_betaIntegral_of_re_pos, Complex.GammaSeq_mul, Complex.Gamma_eq_zero_iff, Complex.differentiable_one_div_Gamma, Real.doublingGamma, Real.doublingGamma_eq_Gamma, Real.Gamma_mul_Gamma_add_half_of_pos, Complex.Gammaℝ, Complex.Gammaℂ, Complex.Gammaℝ_mul_Gammaℝ_add_one, Complex.Gammaℝ_one_sub_mul_Gammaℝ_one_add, HasMellin, mellinInv, Complex.VerticalIntegrable, mellin_cpow_smul, mellin_comp_mul_left, mellin_comp_rpow, mellin_differentiableAt_of_isBigO_rpow, mellin_eq_fourier, mellinInv_eq_fourierInv, Complex.GammaIntegral_eq_mellin, Complex.summable_one_div_nat_cpow]
  E1: auto
families: []
requires: [V19.C03, V19.C04, V17.C07, V18.C05, V18.C06, V15.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The beta function, the reflection formula and the Mellin transform

### Overview

This section proves the main identities of $\Gamma$. The beta integral is a quotient of gamma values. The Gauss limit and Euler's product for the sine give the reflection formula $\Gamma(s) \Gamma(1 - s) = \pi / \sin \pi s$, so $1/\Gamma$ is entire. The Bohr-Mollerup theorem gives the duplication formula. The last part defines the Mellin transform and its inversion along a vertical line.

### Definitions

**Definition (Beta integral).** For $\operatorname{Re} u > 0$ and $\operatorname{Re} v > 0$, let $B(u, v) = \int_0^1 x^{u - 1} (1 - x)^{v - 1} \, dx$. It converges as in Section 1, Theorem 1.

**Definition (Gauss sequence).** For $n \ge 1$, let $G_n(s) = \dfrac{n^s \, n!}{s (s + 1) \cdots (s + n)}$.

**Definition (Mellin transform).** Let $f : (0, \infty) \to \mathbb{C}$. Its Mellin transform at $s \in \mathbb{C}$ is
$$\mathcal{M} f(s) = \int_0^\infty t^{s - 1} f(t) \, dt,$$
which converges at $s$ when $t^{s - 1} f(t)$ is integrable. For $\sigma \in \mathbb{R}$ and $F$ on the line $\operatorname{Re} s = \sigma$, the inverse transform is
$$\mathcal{M}^{-1}_\sigma F(x) = \frac{1}{2\pi} \int_{-\infty}^{\infty} x^{-(\sigma + iy)} F(\sigma + iy) \, dy.$$

**Definition (Archimedean gamma factors).** $\Gamma_\mathbb{R}(s) = \pi^{-s/2} \Gamma(s/2)$ and $\Gamma_\mathbb{C}(s) = 2 (2\pi)^{-s} \Gamma(s)$.

::: mathlib
`mellin` · `Mathlib.Analysis.MellinTransform`

`MellinConvergent f s` is the integrability, and `HasMellin f s m` says that the transform converges with value `m`. `mellinInv σ F x` is the inverse integral, and `Complex.VerticalIntegrable F σ` says that `F` is integrable on the line `re s = σ`.

<?decl mellin?>
<?decl MellinConvergent?>
:::

### Theorems and proofs

**Theorem 1 (Beta and gamma).** For $\operatorname{Re} s > 0$ and $\operatorname{Re} t > 0$, $\Gamma(s) \Gamma(t) = \Gamma(s + t) B(s, t)$.

*Proof.* By Fubini's theorem (Volume 18, Chapter 6, Section 2),
$$\Gamma(s) \Gamma(t) = \int_0^\infty \int_0^\infty x^{s - 1} y^{t - 1} e^{-x - y} \, dy \, dx.$$
It applies because the integral of the modulus is $\Gamma(\operatorname{Re} s) \Gamma(\operatorname{Re} t)$. Substitute $y = x v$ in the inner integral and exchange the order again:
$$\Gamma(s) \Gamma(t) = \int_0^\infty v^{t - 1} \int_0^\infty x^{s + t - 1} e^{-x (1 + v)} \, dx \, dv = \Gamma(s + t) \int_0^\infty \frac{v^{t - 1}}{(1 + v)^{s + t}} \, dv.$$
The inner integral comes from $x = w / (1 + v)$. Last, $v = u / (1 - u)$, with $dv = du / (1 - u)^2$ and $1 + v = 1/(1 - u)$, turns the integral in $v$ into $B(t, s)$, and $u \mapsto 1 - u$ shows $B(t, s) = B(s, t)$. $\square$

::: mathlib
`Complex.Gamma_mul_Gamma_eq_betaIntegral` · `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`

`Complex.betaIntegral u v` is the interval integral from $0$ to $1$. `Complex.betaIntegral_convergent` is its convergence and `Complex.betaIntegral_symm` the symmetry.

<?decl Complex.betaIntegral?>
<?decl Complex.Gamma_mul_Gamma_eq_betaIntegral?>
:::

**Theorem 2 (Gauss limit).** For every $s \notin \{0, -1, -2, \dots\}$, $G_n(s) \to \Gamma(s)$.

*Proof.* Let $\operatorname{Re} s > 0$. Theorem 1 with $t = n + 1$ and Section 1, Theorem 3 give $B(s, n + 1) = n! \, \Gamma(s) / \Gamma(s + n + 1) = n! / (s (s + 1) \cdots (s + n))$. With $x = t / n$,
$$G_n(s) = n^s B(s, n + 1) = \int_0^n t^{s - 1} \Big(1 - \frac{t}{n}\Big)^n dt.$$
The integrand, extended by $0$ for $t > n$, tends to $t^{s - 1} e^{-t}$, with modulus at most $t^{\operatorname{Re} s - 1} e^{-t}$ because $1 - u \le e^{-u}$. Dominated convergence (Volume 18, Chapter 5, Section 3) gives $G_n(s) \to \Gamma(s)$.

For other $s$, a computation from the definition gives $G_n(s) = G_n(s + 1) \cdot \dfrac{s + n + 1}{n s}$. If the limit holds at $s + 1$, then $G_n(s) \to \Gamma(s + 1) / s = \Gamma(s)$. Induction on the number of steps to the half plane ends the proof. $\square$

::: mathlib
`Complex.GammaSeq_tendsto_Gamma` · `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`

`Complex.GammaSeq s n` is $G_n(s)$, and `Complex.GammaSeq_eq_betaIntegral_of_re_pos` is $G_n(s) = n^s B(s, n + 1)$. The limit holds for all `s`, with junk values at the poles.

<?decl Complex.GammaSeq_tendsto_Gamma?>
:::

**Theorem 3 (Reflection formula).** For $s \in \mathbb{C} \setminus \mathbb{Z}$, $\Gamma(s) \Gamma(1 - s) = \dfrac{\pi}{\sin \pi s}$.

*Proof.* From the definition, for $n \ge 1$,
$$G_n(s) \, G_n(1 - s) = \frac{n}{n + 1 - s} \cdot \frac{1}{s \prod_{j = 1}^{n} (1 - s^2 / j^2)}.$$
The first factor tends to $1$, and by Euler's product $\sin \pi s = \pi s \prod_{j \ge 1} (1 - s^2 / j^2)$ the second tends to $\pi / \sin \pi s$. Apply Theorem 2 at $s$ and $1 - s$. $\square$

::: mathlib
`Complex.Gamma_mul_Gamma_one_sub` · `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`

The statement holds for all `z`, because at integers both sides are $0$ in Lean. The product identity is `Complex.GammaSeq_mul`, and Euler's sine product is `Complex.tendsto_euler_sin_prod`.

<?decl Complex.Gamma_mul_Gamma_one_sub?>
<?decl Complex.tendsto_euler_sin_prod?>
:::

**Corollary 4 (No zeros).** $\Gamma(s) \ne 0$ for $s \notin \{0, -1, \dots\}$, and $1/\Gamma$ extends to an entire function with simple zeros at $0, -1, -2, \dots$ and no other zeros.

*Proof.* For $s \notin \mathbb{Z}$, the right side of Theorem 3 is not $0$, and $\Gamma(n) = (n - 1)! \ne 0$ for $n \ge 1$. So $1/\Gamma$ is holomorphic away from the poles. At $-m$, $(s + m) \Gamma(s)$ has a limit $c \ne 0$ by Section 1, Theorem 3, so $1/\Gamma(s) = (s + m) \cdot ((s + m)\Gamma(s))^{-1} \to 0$. The singularity is removable (Chapter 3, Section 3), with a simple zero. $\square$

::: mathlib
`Complex.Gamma_ne_zero` · `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`

`Complex.Gamma_eq_zero_iff` states `Gamma s = 0 ↔ ∃ m : ℕ, s = -m`, which describes the junk values. `Complex.differentiable_one_div_Gamma` says that `(Gamma s)⁻¹` is entire: at a pole, `(0 : ℂ)⁻¹ = 0` is the correct value.

<?decl Complex.Gamma_ne_zero?>
:::

**Theorem 5 (Duplication formula).** For $s \notin \tfrac12 \{0, -1, -2, \dots\}$, $\Gamma(s) \Gamma(s + \tfrac12) = 2^{1 - 2s} \sqrt{\pi} \, \Gamma(2s)$.

*Proof.* For $x > 0$ let $D(x) = 2^{x - 1} \Gamma(x/2) \Gamma(x/2 + 1/2) / \sqrt{\pi}$. Then $D(1) = \Gamma(1/2)/\sqrt\pi = 1$, and $D(x + 1) = x D(x)$ by $\Gamma(x/2 + 1) = (x/2)\Gamma(x/2)$. $\log D$ is a linear function plus two convex functions. The Bohr-Mollerup theorem (Section 1, Theorem 7) gives $D = \Gamma$ on $(0, \infty)$. Put $x = 2s$. Both sides are holomorphic on the connected set where they are defined, so the identity theorem (Volume 17, Chapter 7) extends the formula from $s > 0$. $\square$

::: mathlib
`Complex.Gamma_mul_Gamma_add_half` · `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`

`Real.doublingGamma` is the function $D$, `Real.doublingGamma_eq_Gamma` is the Bohr-Mollerup step and `Real.Gamma_mul_Gamma_add_half_of_pos` the real formula.

<?decl Complex.Gamma_mul_Gamma_add_half?>
:::

**Theorem 6 (Gamma factors).** $\Gamma_\mathbb{R}(s) \Gamma_\mathbb{R}(s + 1) = \Gamma_\mathbb{C}(s)$, and $\Gamma_\mathbb{R}(1 - s) \Gamma_\mathbb{R}(1 + s) = 1 / \cos(\pi s / 2)$.

*Proof.* The first is Theorem 5 at $s/2$, multiplied by $\pi^{-s - 1/2}$. The second is Theorem 3 at $(1 + s)/2$, because $\sin(\pi (1 + s)/2) = \cos(\pi s / 2)$. $\square$

::: mathlib
`Complex.Gammaℝ` · `Mathlib.Analysis.SpecialFunctions.Gamma.Deligne`

`Complex.Gammaℂ` is the other factor. The identities are `Complex.Gammaℝ_mul_Gammaℝ_add_one` and `Complex.Gammaℝ_one_sub_mul_Gammaℝ_one_add`.

<?decl Complex.Gammaℝ?>
:::

**Theorem 7 (Strip of convergence).** Let $f$ be locally integrable on $(0, \infty)$, with $f(t) = O(t^{-a})$ as $t \to \infty$ and $f(t) = O(t^{-b})$ as $t \to 0$, where $b < a$. Then $\mathcal{M} f$ converges and is holomorphic on the strip $b < \operatorname{Re} s < a$.

*Proof.* Let $\sigma = \operatorname{Re} s$. For large $t$, $|t^{s - 1} f(t)| \le C t^{\sigma - a - 1}$, and for small $t$ it is at most $C t^{\sigma - b - 1}$. Both are integrable as $b < \sigma < a$. Holomorphy follows by differentiation under the integral sign, as in Section 1, Theorem 3, Step 1. $\square$

::: mathlib
`mellinConvergent_of_isBigO_rpow` · `Mathlib.Analysis.MellinTransform`

`mellin_differentiableAt_of_isBigO_rpow` gives holomorphy. The rules of change of variable include `mellin_cpow_smul`, `mellin_comp_mul_left` ($\mathcal{M}(f(a t))(s) = a^{-s} \mathcal{M} f(s)$) and `mellin_comp_rpow`. `Complex.GammaIntegral_eq_mellin` says $\Gamma = \mathcal{M}(e^{-t})$ on $\operatorname{Re} s > 0$.

<?decl mellinConvergent_of_isBigO_rpow?>
:::

**Theorem 8 (Mellin inversion).** Let $\mathcal{M} f$ converge at $\sigma$, let $y \mapsto \mathcal{M} f(\sigma + iy)$ be integrable, and let $f$ be continuous at $x > 0$. Then $\mathcal{M}^{-1}_\sigma (\mathcal{M} f)(x) = f(x)$.

*Proof.* The substitution $t = e^{-u}$ gives
$$\mathcal{M} f(\sigma + iy) = \int_{-\infty}^\infty e^{-\sigma u} f(e^{-u}) \, e^{-iyu} \, du,$$
the Fourier transform of $g(u) = e^{-\sigma u} f(e^{-u})$ at $y$. Similarly, $\mathcal{M}^{-1}_\sigma$ is $x^{-\sigma}$ times an inverse Fourier transform at $u = -\log x$. Fourier inversion at a point of continuity ends the proof. $\square$

::: mathlib
`mellinInv_mellin_eq` · `Mathlib.Analysis.MellinInversion`

`mellin_eq_fourier` and `mellinInv_eq_fourierInv` are the two substitutions, with the Mathlib normalization $e^{-2\pi i \xi u}$.

<?decl mellinInv_mellin_eq?>
:::

### Examples

**Example (Beta at one half).** $B(\tfrac12, \tfrac12) = \int_0^1 \frac{dx}{\sqrt{x(1 - x)}} = \pi$, by $x = \sin^2 \theta$. Theorem 1 gives $\Gamma(\tfrac12)^2 = \Gamma(1) \pi$, so $\Gamma(\tfrac12) = \sqrt\pi$, because $\Gamma(\tfrac12) > 0$.

**Example (The Gaussian and the zeta function).** By `mellin_comp_rpow` and `mellin_comp_mul_left`, $\mathcal{M}(e^{-\pi t^2})(s) = \tfrac12 \Gamma_\mathbb{R}(s)$. Similarly $\mathcal{M}(e^{-nt})(s) = n^{-s} \Gamma(s)$, and $\frac{1}{e^t - 1} = \sum_{n \ge 1} e^{-nt}$. The series $\sum n^{-s}$ converges absolutely exactly for $\operatorname{Re} s > 1$ (`Complex.summable_one_div_nat_cpow`), and there dominated convergence gives $\mathcal{M}\big(\tfrac{1}{e^t - 1}\big)(s) = \Gamma(s) \zeta(s)$, with $\zeta(s) = \sum_{n \ge 1} n^{-s}$.

::: mathlib
`riemannZeta` · `Mathlib.NumberTheory.LSeries.RiemannZeta`

`riemannZeta_one_sub` is the functional equation of zeta, which contains $\Gamma(s) \cos(\pi s/2)$.

<?decl riemannZeta?>
:::

### The library around it

`Gamma.Beta` has Theorems 1 to 5 and `Gamma.Deligne` Theorem 6. `MellinInversion` depends on the Fourier transform.

Common errors of a learner:

- Using `mellin f s` without `MellinConvergent f s`. Outside the strip the value is $0$.
- Forgetting the factor $\frac{1}{2\pi}$ and the scaling $y \mapsto 2\pi y$ between `mellinInv` and the Fourier transform.

### Exercises

1. (A) Show that $B(u, 1) = 1/u$ and $B(m, n) = \dfrac{(m - 1)! (n - 1)!}{(m + n - 1)!}$ for $m, n \ge 1$.
2. (A) Compute $\Gamma(\tfrac14) \Gamma(\tfrac34)$.
3. (B) Show that $|\Gamma(\tfrac12 + iy)|^2 = \pi / \cosh \pi y$ for real $y$. Hint: Section 1, Theorem 5 and Theorem 3.
4. (B) Find the strip of convergence and the Mellin transform of $f(t) = \dfrac{1}{1 + t}$. Hint: Theorem 1 and Theorem 3.
5. (C) Prove the identity $\Gamma(s) \zeta(s) = \mathcal{M}\big(\tfrac{1}{e^t - 1}\big)(s)$ for $\operatorname{Re} s > 1$ in detail, and show that the Mellin transform of $\tfrac{1}{e^t - 1}$ does not converge for any $s$ with $\operatorname{Re} s \le 1$. Hint: near $t = 0$, $\tfrac{1}{e^t - 1} \ge \tfrac{1}{2t}$.

### Notes and history

Euler found the beta integral and the reflection formula. The duplication formula carries the name of Legendre. Riemann's 1859 paper on prime numbers uses the integral $\Gamma(s) \zeta(s) = \int_0^\infty \frac{t^{s - 1}}{e^t - 1} dt$. Mellin studied the transform at the end of the nineteenth century. The notation $\Gamma_\mathbb{R}$ and $\Gamma_\mathbb{C}$ follows Deligne.

### Reference

<?reference?>
