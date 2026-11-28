---
title: Power series, the sine product and the cotangent
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Meromorphic
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
explains:
  E2: [Real.hasSum_cos, Real.sinc_le_one, Real.cos_le_sinc, Complex.cot_eq_exp_ratio, Real.tendsto_euler_sin_prod, cotTerm_identity, logDeriv_sin_div_eq_cot, cot_series_rep]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C03, V15.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Power series, the sine product and the cotangent

### Overview

Section 1 of this chapter defines the sine and the cosine from the complex exponential. Section 2 studies the tangent and the inverse functions on the real line. This section collects the modules that describe the trigonometric functions in three other forms: as sums of power series, as an infinite product, and as a sum of simple fractions. It also treats the function $\sin x / x$ and the complex tangent as a function with poles.

The results are classical. The power series $\cos x = \sum (-1)^n x^{2n}/(2n)!$ follows from the series of $\exp$. Euler's product $\sin \pi z = \pi z \prod_{n \ge 1} (1 - z^2/n^2)$ comes from a recurrence for integrals of the same kind as the Wallis integrals of Chapter 7. The logarithmic derivative of the product gives the partial fraction expansion $\pi \cot \pi z = 1/z + \sum_{n \ge 1} \bigl(1/(z - n) + 1/(z + n)\bigr)$. Later volumes use this expansion for the values $\zeta(2k)$ and for the $q$-expansion of Eisenstein series.

The modules work over $\mathbb{C}$ when the statement is about products, poles or derivatives in the complex sense. The real statements follow by restriction. Several results take a hypothesis `x ∈ Complex.integerComplement`, the set of complex numbers that are not integers.

### The library around it

#### The power series of the four functions

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Series` gives each of $\sin$, $\cos$, $\sinh$ and $\cosh$ as the sum of its Taylor series at $0$, over $\mathbb{R}$ and over $\mathbb{C}$. The names follow one pattern. A name `hasSum_f` states `HasSum` of the series to the value, and a name `f_eq_tsum` states the value as a `tsum`. The prefix `Real.` or `Complex.` gives the field.

| Lean name | Statement |
|---|---|
| `Real.hasSum_cos` | $\sum_{n \ge 0} (-1)^n r^{2n}/(2n)! = \cos r$ |
| `Real.hasSum_sin` | $\sum_{n \ge 0} (-1)^n r^{2n+1}/(2n+1)! = \sin r$ |
| `Real.hasSum_cosh` | $\sum_{n \ge 0} r^{2n}/(2n)! = \cosh r$ |
| `Real.hasSum_sinh` | $\sum_{n \ge 0} r^{2n+1}/(2n+1)! = \sinh r$ |
| `Complex.hasSum_cos'` | $\sum_{n \ge 0} (iz)^{2n}/(2n)! = \cos z$ |
| `Complex.hasSum_sin'` | $\sum_{n \ge 0} (iz)^{2n+1}/((2n+1)!\, i) = \sin z$ |

The same statements exist for `Complex.hasSum_cos`, `Complex.hasSum_sin`, `Complex.hasSum_cosh` and `Complex.hasSum_sinh`, and in `tsum` form as `Real.cos_eq_tsum`, `Real.sin_eq_tsum`, `Complex.cos_eq_tsum`, `Complex.sinh_eq_tsum` and the others. The primed complex forms keep the factor $i$ inside the power, and they are the step from the exponential series to the unprimed forms.

**Theorem.** For real $r$, $\cos r = \sum_{n \ge 0} (-1)^n r^{2n}/(2n)!$.

*Proof sketch.* By definition $\cos z = (e^{iz} + e^{-iz})/2$. The series of $e^{iz}$ and $e^{-iz}$ converge absolutely. In their sum the terms of odd degree cancel and the terms of even degree double, so $\cos z = \sum (iz)^{2n}/(2n)!$. This is `Complex.hasSum_cos'`. Since $(iz)^{2n} = (-1)^n z^{2n}$, this is the complex series. For real $r$ all terms are real, and the real part of a convergent series is the series of the real parts. $\square$

One inequality in the module uses the series: `Real.cosh_le_exp_half_sq` states $\cosh x \le e^{x^2/2}$. Compare the two series term by term: $(2n)! \ge 2^n n!$, so $x^{2n}/(2n)! \le (x^2/2)^n/n!$.

#### The function sinc

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc` defines `Real.sinc`, the unnormalized sinc function. Its value is $\sin x / x$ for $x \neq 0$ and $1$ at $0$ (`Real.sinc_apply`, `Real.sinc_of_ne_zero`, `Real.sinc_zero`). The value at $0$ is not a junk value: it is the limit, and `Real.continuous_sinc` states that `Real.sinc` is continuous on all of $\mathbb{R}$. The module proves this with `Real.sinc_eq_dslope`: `Real.sinc` is `dslope Real.sin 0`, the slope function of Chapter 3, whose value at the base point is the derivative $\sin'(0) = 1$.

The function is even (`Real.sinc_neg`). Its bounds are `Real.sinc_le_one`, `Real.neg_one_le_sinc`, `Real.abs_sinc_le_one`, the decay `Real.sinc_le_inv_abs` ($\operatorname{sinc} x \le 1/|x|$ for $x \neq 0$), and the positivity `Real.sinc_pos` on $(-\pi, \pi)$. The lemma `Real.sin_div_le_inv_abs` states the decay for the quotient $\sin x / x$ itself, with no hypothesis, since at $0$ the quotient is the junk value $0$.

**Theorem.** For all $x$, $\operatorname{sinc} x \le 1$. For $|x| < \pi/2$, $\cos x \le \operatorname{sinc} x$.

*Proof.* Both functions are even, so take $x > 0$; at $x = 0$ both claims hold since $\cos 0 = 1$. For $x > 0$, $\sin x \le x$ (`Real.sin_le`), so $\sin x / x \le 1$. For $0 < x < \pi/2$, $x \le \tan x$ (`Real.le_tan`). Multiply by $\cos x / x > 0$: $\cos x \le \sin x / x$. $\square$

The two bounds squeeze $\sin x / x$ between $\cos x$ and $1$ near $0$. This gives the limit $\sin x / x \to 1$ again, the result `Real.tendsto_sin_div_nhdsNE_zero` of Section 1.

#### The complex tangent

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv` treats `Complex.tan`, which is `Complex.sin x / Complex.cos x` (`Complex.tan_eq_sin_div_cos`). The derivative is $1/\cos^2 x$ where $\cos x \neq 0$: `Complex.hasDerivAt_tan`, `Complex.hasStrictDerivAt_tan` and `Complex.deriv_tan`. The regularity results are equivalences, and each has the same right side: `Complex.differentiableAt_tan`, `Complex.continuousAt_tan` and `Complex.contDiffAt_tan` all state their property at $x$ if and only if $\cos x \neq 0$. At a zero of the cosine the norm of the tangent tends to infinity: `Complex.tendsto_norm_tan_of_cos_eq_zero`, and `Complex.tendsto_norm_tan_atTop` for the points $(2k + 1)\pi/2$ by name. The limit `Complex.tendsto_tan_div_nhdsNE_zero` states $\tan z / z \to 1$ as $z \to 0$, $z \neq 0$.

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Meromorphic` places the tangent and the hyperbolic tangent in the theory of meromorphic functions of Volume 19. `Complex.meromorphicAt_tan` and `Complex.meromorphic_tan` state that `Complex.tan` is meromorphic at each point and on all of $\mathbb{C}$; `Complex.meromorphicAt_tanh` and `Complex.meromorphic_tanh` state the same for `Complex.tanh`. The stronger `Complex.meromorphicNFOn_tan` states that `Complex.tan` is in normal form on all of $\mathbb{C}$: at each pole its value is $0$, and it has no removable singularity. This fits the junk value of the division, since $\sin x / 0 = 0$ in Lean.

#### Euler's product for the sine

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd` proves
$$\sin \pi z = \pi z \prod_{n = 1}^{\infty} \Bigl(1 - \frac{z^2}{n^2}\Bigr)$$
for all complex $z$, as a limit of partial products: `Complex.tendsto_euler_sin_prod`, and `Real.tendsto_euler_sin_prod` for real $x$. The partial product has the index `j ∈ Finset.range n` and the factor `1 - z ^ 2 / (j + 1) ^ 2`, so the shift by one is in the factor.

**Theorem.** For real $x$, $\pi x \prod_{j < n} \bigl(1 - x^2/(j+1)^2\bigr) \to \sin \pi x$.

*Proof sketch.* Put $A_n(z) = \int_0^{\pi/2} \cos(2zt) \cos^{n} t \, dt$ and $B_n = A_n(0)$. Two integrations by parts (`EulerSine.integral_cos_mul_cos_pow_aux` and `EulerSine.integral_sin_mul_sin_mul_cos_pow_eq`) give the recurrence `EulerSine.integral_cos_mul_cos_pow_even`:
$$\Bigl(1 - \frac{z^2}{(n+1)^2}\Bigr) A_{2n+2}(z) = \frac{2n+1}{2n+2} A_{2n}(z).$$
The same recurrence holds for $B_n$ with $z = 0$, so the ratio of the two gives a factor $1 - z^2/(n+1)^2$ at each step. Since $A_0(z) = \sin(\pi z)/(2z)$ and $B_0 = \pi/2$, induction gives `EulerSine.sin_pi_mul_eq`:
$$\sin \pi z = \pi z \prod_{j < n} \Bigl(1 - \frac{z^2}{(j+1)^2}\Bigr) \cdot \frac{A_{2n}(z)}{B_{2n}}.$$
The weight $\cos^{2n} t$ concentrates at $t = 0$ as $n$ grows. So for a continuous $f$ on $[0, \pi/2]$ the weighted mean $\int \cos^n t\, f(t)\,dt / \int \cos^n t\,dt$ tends to $f(0)$ (`EulerSine.tendsto_integral_cos_pow_mul_div`). With $f(t) = \cos(2zt)$ the last factor tends to $1$. $\square$

The proof uses `EulerSine.integral_cos_pow_pos` to divide by $B_n$, and `EulerSine.integral_cos_pow_eq` to compare $B_n$ with the Wallis integrals $\int_0^\pi \sin^n t\,dt$ of Chapter 7.

#### The cotangent

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent` turns the product into a series. It names the terms of the product and of the series by two abbreviations: `sineTerm x n` is $-x^2/(n+1)^2$, so the factor is `1 + sineTerm x n`, and `cotTerm x n` is $1/(x - (n+1)) + 1/(x + (n+1))$.

The product converges in the sense of infinite products of Volume 14. `multipliable_sineTerm` states that it is `Multipliable`, `euler_sineTerm_tprod` gives the value of the `tprod` for $x \neq 0$, and `tendsto_euler_sin_prod'` states the limit of the partial products of $\sin(\pi x)/(\pi x)$. The convergence is uniform on compact sets: `multipliableUniformlyOn_euler_sin_prod_on_compact`, `HasProdUniformlyOn_sineTerm_prod_on_compact`, and `HasProdLocallyUniformlyOn_euler_sin_prod` on the set $\mathbb{C} \setminus \{0\}$.

**Theorem.** For $x$ not an integer, $\frac{d}{dx} \log \frac{\sin \pi x}{\pi x} = \pi \cot \pi x - \frac{1}{x}$, and $\mathrm{cotTerm}(x, n) = \frac{2x}{(x + n + 1)(x - n - 1)}$.

*Proof.* The logarithmic derivative $f'/f$ of a quotient is the difference of the two logarithmic derivatives. The one of $\sin \pi x$ is $\pi \cos \pi x / \sin \pi x = \pi \cot \pi x$, and the one of $\pi x$ is $1/x$. The hypothesis gives $\sin \pi x \neq 0$ (`sin_pi_mul_ne_zero`). For the second claim, put $m = n + 1$ and add the two fractions: $\frac{1}{x - m} + \frac{1}{x + m} = \frac{(x + m) + (x - m)}{(x - m)(x + m)}$. $\square$

These are `logDeriv_sin_div_eq_cot` and `cotTerm_identity`. Mathlib writes the logarithmic derivative $f'/f$ as `logDeriv`. The logarithmic derivative of a finite product is the sum of the logarithmic derivatives, so the one of the $n$th partial product is $\sum_{j < n} \mathrm{cotTerm}(x, j)$ (`logDeriv_sineTerm_eq_cotTerm` and `logDeriv_prod_sineTerm_eq_sum_cotTerm`).

**Theorem (Mittag-Leffler expansion of the cotangent).** For $x \in \mathbb{C} \setminus \mathbb{Z}$,
$$\pi \cot \pi x = \frac{1}{x} + \sum_{n = 1}^{\infty} \Bigl(\frac{1}{x - n} + \frac{1}{x + n}\Bigr).$$

*Proof sketch.* The partial products converge to $\sin(\pi x)/(\pi x)$ locally uniformly on $\mathbb{C} \setminus \{0\}$. By the theorem of Weierstrass of Volume 19, a locally uniform limit of holomorphic functions has as derivative the limit of the derivatives. So the logarithmic derivatives converge as well (`tendsto_logDeriv_euler_sin_div`). By the previous theorem the limit of $\sum_{j < n} \mathrm{cotTerm}(x, j)$ is $\pi \cot \pi x - 1/x$ (`tendsto_logDeriv_euler_cot_sub`). The series is summable (`summable_cotTerm`), since by `cotTerm_identity` its terms are $O(1/n^2)$. $\square$

This is `cot_series_rep`, with the sum over `n : ℕ+`. The variant `cot_series_rep'` has the sum over `n : ℕ` with the shift `n + 1` and the term $1/x$ on the left.

On the upper half plane the module gives two more forms. With $q = e^{2\pi i z}$ and $\operatorname{Im} z > 0$, so that $|q| < 1$, `pi_mul_cot_pi_q_exp` states $\pi \cot \pi z = \pi i - 2\pi i \sum_{n \ge 0} q^n$. It follows from `Complex.cot_eq_exp_ratio` and its variant `Complex.cot_pi_eq_exp_ratio` and a geometric series. The derivatives of order $k \ge 1$ are `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`:
$$\frac{d^k}{dz^k}\, \pi \cot \pi z = (-1)^k k! \sum_{n \in \mathbb{Z}} \frac{1}{(z + n)^{k+1}}.$$
The proof differentiates the Mittag-Leffler series term by term. The lemmas `eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet` and `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm` give the derivatives of the terms and the locally uniform convergence. The derivatives use `iteratedDerivWithin` on `UpperHalfPlane.upperHalfPlaneSet`, because the Eisenstein series of the theory of modular forms live there.

**Theorem.** For all $z$, $\cot z = \dfrac{e^{2iz} + 1}{i\,(1 - e^{2iz})}$.

*Proof.* Write $w = e^{iz}$. Then $\cos z = (w + w^{-1})/2$ and $\sin z = (w - w^{-1})/(2i)$, so $\cot z = i(w + w^{-1})/(w - w^{-1}) = i(w^2 + 1)/(w^2 - 1)$. Since $i/(w^2 - 1) = 1/(i(1 - w^2))$, this is the claim. When $\sin z = 0$, both sides are the junk value $0$, since $w^2 = 1$ and Lean divides by $0$. $\square$

#### Common errors

1. Using `cot_series_rep` at an integer. The hypothesis `x ∈ Complex.integerComplement` excludes all integers, also $0$; at an integer the left side is the junk value $0$ and the series has a term with division by zero.
2. Reading `Real.sinc` as the normalized function $\sin(\pi x)/(\pi x)$. Mathlib uses the unnormalized form $\sin x / x$, with zeros at the nonzero multiples of $\pi$.
3. Expecting `Complex.continuousAt_tan` to be an implication. It is an equivalence with `Complex.cos x ≠ 0`, so it also proves that the tangent is not continuous at a pole.

### Exercises

1. (A) Use `Real.hasSum_sin` to show that $|\sin x - x + x^3/6| \le |x|^5/120$ for $|x| \le 1$. Hint: the series alternates with decreasing terms.
2. (A) Show that `Real.sinc` is differentiable at every $x \ne 0$ and compute its derivative there.
3. (B) Put $z = 1/2$ in Euler's product and deduce Wallis's product $\prod_{n \ge 1} \frac{4n^2}{4n^2 - 1} = \frac{\pi}{2}$.
4. (B) Compare the coefficient of $z^3$ in the power series of $\sin \pi z$ and in Euler's product, and deduce $\sum_{n \ge 1} 1/n^2 = \pi^2/6$. Explain which step of this argument needs more than the convergence of the partial products.
5. (A) Show from `Real.hasSum_cosh` that $\cosh x \ge 1 + x^2/2$ for all real $x$, and that $\cosh$ is increasing on $[0, \infty)$.
6. (C) Differentiate the Mittag-Leffler expansion once and deduce $\sum_{n \in \mathbb{Z}} \frac{1}{(z + n)^2} = \frac{\pi^2}{\sin^2 \pi z}$ for $z \notin \mathbb{Z}$.

### Reference

<?reference?>
