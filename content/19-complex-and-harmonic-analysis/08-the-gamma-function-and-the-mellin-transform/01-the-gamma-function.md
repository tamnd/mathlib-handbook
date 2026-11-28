---
title: The gamma function
kind: theory
modules:
  - Mathlib.Analysis.SpecialFunctions.Gamma.Basic
  - Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
  - Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
  - Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
  - Mathlib.Analysis.Meromorphic.Complex
  - Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
  - Mathlib.Analysis.SpecialFunctions.Stirling
explains:
  E3: [Complex.Gamma, Complex.GammaIntegral, Complex.GammaIntegral_convergent, Complex.Gamma_add_one, Complex.Gamma_nat_eq_factorial, Complex.differentiableAt_Gamma, Real.convexOn_log_Gamma, Real.BohrMollerup.tendsto_logGammaSeq, Complex.digamma]
  E2: [Complex.partialGamma, Complex.partialGamma_add_one, Complex.tendsto_partialGamma, Complex.GammaIntegral_add_one, Complex.Gamma_eq_integral, Complex.Gamma_zero, Complex.Gamma_neg_nat_eq_zero, Complex.Gamma_conj, Complex.Gamma_ofReal, Real.Gamma, Real.Gamma_pos_of_pos, Complex.hasDerivAt_Gamma_of_re_pos, Complex.tendsto_self_mul_Gamma_nhds_zero, Complex.not_continuousAt_Gamma_neg_nat, Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma, Real.BohrMollerup.logGammaSeq, Real.BohrMollerup.f_add_nat_le, Real.BohrMollerup.f_add_nat_ge, Real.BohrMollerup.tendsto_log_gamma, Complex.digamma_def, Complex.digamma_apply_add_one, Complex.digamma_one, Complex.digamma_nat_add_one, Meromorphic.Gamma, MeromorphicNFOn.Gamma]
  E1: auto
families: []
requires: [V19.C02, V19.C04, V18.C05, V18.C06, V18.C07, V15.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The gamma function

### Overview

The gamma function extends the factorial: $\Gamma(n + 1) = n!$ and $\Gamma(s + 1) = s \, \Gamma(s)$. Euler's integral defines $\Gamma$ on the right half plane, and the functional equation continues it to a meromorphic function on $\mathbb{C}$ with simple poles at $0, -1, -2, \dots$. This section proves these facts and the Bohr-Mollerup theorem: the functional equation and the convexity of $\log \Gamma$ determine $\Gamma$ on $(0, \infty)$. It ends with the digamma function.

### Definitions

**Definition (Euler integral).** For $\operatorname{Re} s > 0$, let
$$\Gamma(s) = \int_0^\infty x^{s - 1} e^{-x} \, dx, \qquad x^{s - 1} = e^{(s - 1) \log x}.$$
For $X > 0$, the partial integral is $\gamma(s, X) = \int_0^X x^{s - 1} e^{-x} \, dx$.

**Definition (Gamma function).** For $s \in \mathbb{C}$ not in $\{0, -1, -2, \dots\}$, choose $n \in \mathbb{N}$ with $\operatorname{Re} s + n > 0$ and let
$$\Gamma(s) = \frac{\Gamma(s + n)}{s (s + 1) \cdots (s + n - 1)}.$$
Theorem 3 shows that the value does not depend on $n$.

**Definition (Digamma function).** $\psi(s) = \Gamma'(s) / \Gamma(s)$, the logarithmic derivative of $\Gamma$ (Chapter 4, Section 2).

::: mathlib
`Complex.Gamma` · `Mathlib.Analysis.SpecialFunctions.Gamma.Basic`

`Complex.GammaIntegral s` is the Euler integral and `Complex.partialGamma s X` the partial integral. `Complex.Gamma` is a total function, defined by the formula above. At the poles the formula divides by $0$, which gives the junk value $\Gamma(-m) = 0$ (`Complex.Gamma_zero`, `Complex.Gamma_neg_nat_eq_zero`). `Real.Gamma` agrees with it on real numbers (`Complex.Gamma_ofReal`).

<?decl Complex.Gamma?>
:::

### Theorems and proofs

**Theorem 1 (Convergence).** If $\operatorname{Re} s = \sigma > 0$, the function $x \mapsto x^{s - 1} e^{-x}$ is integrable on $(0, \infty)$.

*Proof.* The modulus is $x^{\sigma - 1} e^{-x}$. On $(0, 1]$ it is at most $x^{\sigma - 1}$, with integral $1 / \sigma$. On $[1, \infty)$ it is at most $C e^{-x / 2}$, because the exponential grows faster than every power (Volume 15, Chapter 5). $\square$

::: mathlib
`Complex.GammaIntegral_convergent` · `Mathlib.Analysis.SpecialFunctions.Gamma.Basic`

`Complex.Gamma_eq_integral` says that `Gamma s = GammaIntegral s` for `0 < s.re`.

<?decl Complex.GammaIntegral_convergent?>
:::

**Theorem 2 (Functional equation).** For $\operatorname{Re} s > 0$, $\Gamma(s + 1) = s \, \Gamma(s)$. So $\Gamma(1) = 1$ and $\Gamma(n + 1) = n!$ for $n \in \mathbb{N}$.

*Proof.* Integrate by parts on $[0, X]$ with $u = x^s$ and $dv = e^{-x} dx$. The boundary term at $0$ is $0$ because $\operatorname{Re} s > 0$, so
$$\gamma(s + 1, X) = s \, \gamma(s, X) - X^s e^{-X}.$$
As $X \to \infty$, $\gamma(s, X) \to \Gamma(s)$ by dominated convergence (Volume 18, Chapter 5, Section 3) and $X^s e^{-X} \to 0$. Next, $\Gamma(1) = \int_0^\infty e^{-x} dx = 1$, and induction gives $\Gamma(n + 1) = n!$. $\square$

::: mathlib
`Complex.Gamma_add_one` · `Mathlib.Analysis.SpecialFunctions.Gamma.Basic`

The steps of the proof are `Complex.partialGamma_add_one`, `Complex.tendsto_partialGamma` and `Complex.GammaIntegral_add_one`. `Gamma_add_one` holds for every `s ≠ 0`, and `Complex.Gamma_nat_eq_factorial` is $\Gamma(n + 1) = n!$.

<?decl Complex.Gamma_add_one?>
<?decl Complex.Gamma_nat_eq_factorial?>
:::

**Theorem 3 (Continuation).** The definition of $\Gamma(s)$ does not depend on $n$. The function $\Gamma$ is holomorphic on $\mathbb{C} \setminus \{0, -1, -2, \dots\}$ and satisfies $\Gamma(s + 1) = s \, \Gamma(s)$ there. At $s = -m$ it has a simple pole with residue $(-1)^m / m!$.

*Proof.* Step 1. On $\operatorname{Re} s > 0$, $\Gamma$ is holomorphic. For $\delta \le \operatorname{Re} s \le A$, the derivative $x^{s - 1} (\log x) e^{-x}$ of the integrand in $s$ has modulus at most $(x^{\delta - 1} + x^{A - 1}) |\log x| e^{-x}$, which is integrable. Differentiation under the integral sign, a form of dominated convergence, gives $\Gamma'(s) = \int_0^\infty x^{s - 1} (\log x) e^{-x} \, dx$.

Step 2. If $\operatorname{Re} s + n > 0$, then $\Gamma(s + n + 1) = (s + n) \Gamma(s + n)$ by Theorem 2, so
$$\frac{\Gamma(s + n + 1)}{s (s + 1) \cdots (s + n)} = \frac{\Gamma(s + n)}{s (s + 1) \cdots (s + n - 1)}.$$
So all admissible $n$ give the same value. On $\operatorname{Re} s > -n$ the formula is a quotient of holomorphic functions, holomorphic away from the zeros $0, \dots, -(n - 1)$ of the denominator. The functional equation follows from the formula.

Step 3. Fix $m$ and take $n = m + 1$. Near $s = -m$,
$$(s + m) \, \Gamma(s) = \frac{\Gamma(s + m + 1)}{s (s + 1) \cdots (s + m - 1)} \longrightarrow \frac{\Gamma(1)}{(-m)(-m + 1) \cdots (-1)} = \frac{(-1)^m}{m!}.$$
The limit is not $0$, so $-m$ is a simple pole with this residue. $\square$

**Corollary 4 (Meromorphy).** $\Gamma$ is meromorphic on $\mathbb{C}$ in the sense of Chapter 4, Section 1, with order $-1$ at each $-m$. $\square$

::: mathlib
`Complex.differentiableAt_Gamma` · `Mathlib.Analysis.SpecialFunctions.Gamma.Deriv`

The hypothesis is `∀ m : ℕ, s ≠ -m`. `Complex.hasDerivAt_Gamma_of_re_pos` is Step 1, and `Complex.tendsto_self_mul_Gamma_nhds_zero` is Step 3 for $m = 0$. `Complex.not_continuousAt_Gamma_neg_nat` says that $\Gamma$ is not continuous at a pole. `Meromorphic.Gamma` is Corollary 4, and `MeromorphicNFOn.Gamma` says that $\Gamma$ is in normal form (Chapter 4, Section 1), which needs the value $0$ at a pole.

<?decl Complex.differentiableAt_Gamma?>
:::

**Theorem 5 (Real values).** $\overline{\Gamma(s)} = \Gamma(\bar s)$. For real $x > 0$, $\Gamma(x)$ is real and $\Gamma(x) > 0$.

*Proof.* For $\operatorname{Re} s > 0$ the integrands are conjugate, and the continuation formula keeps the identity. For $x > 0$ the integrand is positive. $\square$

**Theorem 6 (Log-convexity).** On $(0, \infty)$, $\log \Gamma$ is convex: for $s, t > 0$ and $a, b \ge 0$ with $a + b = 1$, $\Gamma(a s + b t) \le \Gamma(s)^a \, \Gamma(t)^b$.

*Proof.* Let $a, b > 0$ (the cases $a = 0$, $b = 0$ are trivial). Write
$$x^{a s + b t - 1} e^{-x} = \big(x^{s - 1} e^{-x}\big)^a \big(x^{t - 1} e^{-x}\big)^b.$$
Hölder's inequality with $p = 1/a$, $q = 1/b$ (Volume 18, Chapter 7, Section 1) bounds the integral by $\big(\int x^{s - 1} e^{-x}\big)^a \big(\int x^{t - 1} e^{-x}\big)^b$. Take logarithms. $\square$

::: mathlib
`Real.convexOn_log_Gamma` · `Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup`

The Hölder step is `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`. Theorem 5 is `Complex.Gamma_conj` and `Real.Gamma_pos_of_pos`.

<?decl Real.convexOn_log_Gamma?>
:::

**Theorem 7 (Bohr-Mollerup).** Let $f : (0, \infty) \to \mathbb{R}$ be convex, with $f(x + 1) = f(x) + \log x$ for all $x > 0$ and $f(1) = 0$. Then $f = \log \Gamma$, and for $x > 0$,
$$\log \Gamma(x) = \lim_{n \to \infty} \Big( x \log n + \log n! - \sum_{j = 0}^{n} \log(x + j) \Big).$$

*Proof.* Step 1. By induction, $f(n) = \log((n - 1)!)$ and $f(x + n) = f(x) + \sum_{j = 0}^{n - 1} \log(x + j)$.

Step 2. Let $n \ge 2$ and $0 < x \le 1$. The slopes of a convex function increase. Compare the chords on $[n - 1, n]$, $[n, n + x]$ and $[n, n + 1]$:
$$\log(n - 1) = f(n) - f(n - 1) \le \frac{f(n + x) - f(n)}{x} \le f(n + 1) - f(n) = \log n.$$
With Step 1, this gives $L_n(x) + x \log(n - 1) \le f(x) \le L_n(x) + x \log n$, where $L_n(x) = \log((n - 1)!) - \sum_{j = 0}^{n - 1} \log(x + j)$.

Step 3. The two bounds differ by $x \log(n / (n - 1)) \to 0$, and they do not depend on $f$. So $f(x) = \lim_n (L_n(x) + x \log n)$. Replace $n$ by $n + 1$: since $x \log((n + 1)/n) \to 0$, the limit is the limit in the statement. $\log \Gamma$ satisfies the hypotheses by Theorems 2, 5 and 6, so $f = \log \Gamma$ on $(0, 1]$. The functional equation gives equality for all $x > 0$. $\square$

::: mathlib
`Real.BohrMollerup.tendsto_logGammaSeq` · `Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup`

`logGammaSeq x n` is the expression in the limit, and Step 2 is `Real.BohrMollerup.f_add_nat_le` and `Real.BohrMollerup.f_add_nat_ge`. `tendsto_logGammaSeq` gives the limit `f x - f 1`, and `Real.BohrMollerup.tendsto_log_gamma` is the case of $\log \Gamma$. The index of this edition has no declaration for the uniqueness statement.

<?decl Real.BohrMollerup.tendsto_logGammaSeq?>
:::

**Theorem 8 (Digamma).** $\psi(s + 1) = \psi(s) + 1/s$ for $s \notin \{0, -1, \dots\}$, and $\psi(n + 1) = \psi(1) + \sum_{k = 1}^n 1/k$.

*Proof.* Take the logarithmic derivative of $\Gamma(s + 1) = s \, \Gamma(s)$, with the product rule of Chapter 4, Section 2. Induction gives the second formula. $\square$

::: mathlib
`Complex.digamma` · `Mathlib.Analysis.SpecialFunctions.Gamma.Digamma`

`Complex.digamma_def` says `digamma = logDeriv Gamma`, and `Complex.digamma_apply_add_one` is Theorem 8. `Complex.digamma_one` states $\psi(1) = -\gamma$, with `Real.eulerMascheroniConstant` as $\gamma$, and `Complex.digamma_nat_add_one` gives $\psi(n + 1) = H_n - \gamma$.

<?decl Complex.digamma?>
:::

### Examples

**Example (The value at one half).** The substitution $x = u^2$ gives $\Gamma(1/2) = \int_0^\infty x^{-1/2} e^{-x} dx = 2 \int_0^\infty e^{-u^2} du = \sqrt{\pi}$, by the Gaussian integral of Volume 18, Chapter 6, Section 2. The functional equation then gives $\Gamma(3/2) = \sqrt{\pi}/2$ and $\Gamma(-1/2) = \Gamma(1/2)/(-1/2) = -2\sqrt{\pi}$.

::: mathlib
`Real.Gamma_one_half_eq` · `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`

The value is in the file of the Gaussian integral.

<?decl Real.Gamma_one_half_eq?>
:::

**Counterexample (Without log-convexity).** Let $g(x) = \Gamma(x) \, (1 + \tfrac12 \sin 2\pi x)$ on $(0, \infty)$. Then $g > 0$, $g(1) = 1$ and $g(x + 1) = x \, g(x)$, because $\sin 2\pi x$ has period $1$. But $g \ne \Gamma$, for example at $x = 5/4$. So Theorem 7 needs the convexity.

### The library around it

The files follow the order of this section: `Gamma.Basic`, `Gamma.Deriv`, `Gamma.BohrMollerup` and `Gamma.Digamma`.

The module `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` proves the Gaussian integral and its consequences for $\Gamma$. The theorem `integral_gaussian` gives $\int_{\mathbb{R}} e^{-bx^2}\,dx = \sqrt{\pi/b}$, and `integral_gaussian_complex` gives $(\pi/b)^{1/2}$ for $\operatorname{Re} b > 0$, with the principal branch of the square root. The proof computes the square of the integral in polar coordinates, by `integral_gaussian_sq_complex`. The integrability lemmas `integrable_exp_neg_mul_sq` and `integrableOn_rpow_mul_exp_neg_rpow` cover the integrands $x^s e^{-bx^p}$, and `integrable_exp_neg_mul_sq_iff` says that $e^{-bx^2}$ is integrable if and only if $b > 0$. The substitution $t = x^2$ in the Euler integral gives `Real.Gamma_one_half_eq` and `Complex.Gamma_one_half_eq`, and `Real.Gamma_nat_add_half` gives $\Gamma(k + 1/2) = (2k - 1)!! \sqrt{\pi}/2^k$. The module `Mathlib.Analysis.SpecialFunctions.Stirling` proves Stirling's formula for $n!$. It defines `Stirling.stirlingSeq` $n = n!/(\sqrt{2n}(n/e)^n)$, proves that the sequence decreases and is bounded below by a positive constant, and finds its limit $\sqrt{\pi}$ with the Wallis product. This is `Stirling.tendsto_stirlingSeq_sqrt_pi`. The asymptotic form is `Stirling.factorial_isEquivalent_stirling`, $n! \sim \sqrt{2\pi n}(n/e)^n$, and `Stirling.le_factorial_stirling` is the lower bound $\sqrt{2\pi n}(n/e)^n \le n!$ for all $n$.

Common errors of a learner:

- Applying `Complex.Gamma_eq_integral` without `0 < s.re`. On the left half plane the integral diverges.
- Reading the junk value `Complex.Gamma (-m) = 0` as a zero. Section 2 shows that $\Gamma$ has no zeros.
- Writing `Gamma n = n !`. The shift is `Gamma (n + 1) = n !`.

### Exercises

1. (A) Compute $\Gamma(5/2)$ and $\Gamma(-3/2)$ from $\Gamma(1/2) = \sqrt\pi$.
2. (A) Show that $\int_0^\infty x^{n} e^{-a x} dx = n! / a^{n + 1}$ for $a > 0$. Hint: substitute $x = u / a$.
3. (B) Show that $\Gamma(n + \tfrac12) = \dfrac{(2n)!}{4^n \, n!} \sqrt{\pi}$.
4. (B) Show that the function $g$ of the counterexample is not log-convex on $(0, \infty)$. Hint: Theorem 7.
5. (C) Deduce from Theorem 7 the Gauss product $\Gamma(x) = \lim_n \dfrac{n^x \, n!}{x (x + 1) \cdots (x + n)}$ for $x > 0$, and show that the limit is also correct for $-1 < x < 0$. Hint: apply the formula to $x + 1$.

### Notes and history

Euler introduced the gamma function in letters to Goldbach in 1729 and 1730, first as an infinite product and then as an integral. The notation $\Gamma$ is due to Legendre. Bohr and Mollerup proved the characterization by log-convexity in 1922, and Artin made it the basis of his 1931 book on the gamma function.

### Reference

<?reference?>
