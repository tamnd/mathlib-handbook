---
title: Hypergeometric and Bessel functions
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
  - Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
  - Mathlib.Analysis.SpecialFunctions.Bessel
explains:
  E2: [ordinaryHypergeometric, ordinaryHypergeometricSeries_radius_eq_one, ordinaryHypergeometric_radius_top_of_neg_nat₁, Complex.regularizedHGFunCoeff, Complex.regularizedHGFun, Complex.radius_regularizedHGFunSeries_eq_top, Complex.ordinaryHypergeometric_div_Gamma_eq, Complex.besselJ, Complex.besselJ_neg_int, Complex.two_mul_self_mul_besselJ]
  E1: auto
families: []
requires: [V19.C01, V19.C02, V17.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Hypergeometric and Bessel functions

### Overview

Many special functions are power series whose coefficients have a rational ratio: $c_{n+1}/c_n$ is a rational function of $n$. These are the hypergeometric series. The geometric series $\sum z^n$, the exponential, $\log(1 + z)/z$, the arcsine and the Legendre polynomials are all examples. The Bessel functions, which come from the Laplace equation in cylindrical coordinates, are also of this form after a change of variable.

Mathlib has three modules on this subject.

1. `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric` defines the Gauss function ${}_2F_1(a, b; c; x)$ in a Banach algebra over a field, and finds its radius of convergence.
2. `Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric` defines the regularized function ${}_p\tilde{F}_q$ over $\mathbb{C}$ for any numbers $p$ and $q$ of parameters. The regularization divides by the Gamma function of Section 1. It removes the poles at the negative integers.
3. `Mathlib.Analysis.SpecialFunctions.Bessel` defines the Bessel function $J_a$ of the first kind from ${}_0\tilde{F}_1$ and proves its recurrences.

The section uses the ascending Pochhammer symbol $(a)_n = a(a+1)\cdots(a+n-1)$, which is `ascPochhammer`, the formal power series of Volume 17, and the Gamma function of Section 1.

### The library around it

#### The Gauss hypergeometric function

For $a, b, c$ in a field $𝕂$ and $x$ in a topological $𝕂$-algebra $𝔸$, the function `ordinaryHypergeometric a b c x`, with notation `₂F₁ a b c x`, is the sum of the series
$${}_2F_1(a, b; c; x) = \sum_{n \ge 0} \frac{(a)_n (b)_n}{(c)_n}\,\frac{x^n}{n!}.$$
The formal series is `ordinaryHypergeometricSeries 𝔸 a b c`, and `ordinaryHypergeometric_eq_tsum` writes the function as a `tsum`. The value at $0$ is $1$ (`ordinaryHypergeometric_zero`), and the function is symmetric in $a$ and $b$ (`ordinaryHypergeometricSeries_symm`).

The parameter $c$ needs care. If $c = -k$ for a natural number $k$, then $(c)_n = 0$ for $n > k$. In Lean the inverse of $0$ is $0$, so these terms vanish. The classical function is not defined in this case, and Mathlib gives it a junk value: a polynomial. In the same way, $a = -k$ or $b = -k$ make the series a polynomial of degree $k$, as in the classical theory. `ordinaryHypergeometricSeries_eq_zero_iff` states that the $n$-th term vanishes if and only if one of $a, b, c$ is $-k$ with $k < n$.

**Theorem.** Over an `RCLike` field and a normed division ring $𝔸$, if none of $a, b, c$ is a nonpositive integer, the radius of convergence of the series is $1$.

*Proof.* No coefficient vanishes. The ratio of successive coefficients is
$$\frac{|c_n|}{|c_{n+1}|} = \frac{|c + n|\,|1 + n|}{|a + n|\,|b + n|},$$
by `ordinaryHypergeometricSeries_norm_div_succ_norm`. It tends to $1$ as $n \to \infty$. By the ratio test for the radius of a power series, the radius is $1$. $\square$

This is `ordinaryHypergeometricSeries_radius_eq_one`. If one parameter is a nonpositive integer, the series is finite and the radius is $\infty$: `ordinaryHypergeometric_radius_top_of_neg_nat₁`, `ordinaryHypergeometric_radius_top_of_neg_nat₂` and `ordinaryHypergeometric_radius_top_of_neg_nat₃` treat $a$, $b$ and $c$.

#### The regularized hypergeometric function

The module `Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric` works over $\mathbb{C}$ with two multisets of parameters, $a = \{a_1, \ldots, a_p\}$ and $b = \{b_1, \ldots, b_q\}$. The coefficient `Complex.regularizedHGFunCoeff a b n` is
$$C_{a,b}(n) = \frac{\prod_i (a_i)_n}{n! \prod_j \Gamma(b_j + n)}.$$
Since $(b)_n = \Gamma(b + n)/\Gamma(b)$, this is the coefficient of ${}_pF_q$ divided by $\prod_j \Gamma(b_j)$. The function $1/\Gamma$ is entire (Section 2), so the coefficient is defined for all $b$, also at the poles of $\Gamma$. The formal series is `Complex.regularizedHGFunSeries a b`, and the function `Complex.regularizedHGFun a b` is its sum.

The coefficients satisfy a first order recurrence. If no $b_j$ equals $-n$,
$$C_{a,b}(n + 1) = C_{a,b}(n)\,\frac{\prod_i (a_i + n)}{(n + 1)\prod_j (b_j + n)},$$
by `Complex.regularizedHGFunCoeff_add_one`. `Complex.regularizedHGFunCoeff_eq_zero_iff` lists the zero coefficients. With no parameters at all, the series is the exponential series (`Complex.regularizedHGFunSeries_zero_zero`), so `Complex.regularizedHGFun 0 0` is `Complex.exp` (`Complex.regularizedHGFun_zero_zero`).

**Theorem.** If $p \le q$, the series ${}_p\tilde{F}_q$ has infinite radius of convergence, and the function is entire.

*Proof.* If some coefficient vanishes for all large $n$, the series is a polynomial. Otherwise, the ratio $C(n+1)/C(n)$ is a product of $p$ factors of size about $n$ divided by $q + 1$ factors of size about $n$. Since $p < q + 1$, it tends to $0$, and the ratio test gives an infinite radius. A power series with infinite radius is analytic everywhere. $\square$

This is `Complex.radius_regularizedHGFunSeries_eq_top`, with `Complex.analyticOnNhd_regularizedHGFun_of_card_le`. For $p = q + 1$ the radius is at least $1$ (`Complex.radius_regularizedHGFunSeries_ge_one`), and it is $1$ when no $a_i$ is a nonpositive integer (`Complex.radius_regularizedHGFunSeries_eq_one`). Then the function is analytic on the unit disc (`Complex.analyticOnNhd_regularizedHGFun_of_card_eq_add_one`).

The derivative raises every parameter by $1$:
$$\frac{d}{dz}\,{}_p\tilde{F}_q(a; b; z) = \Big(\prod_i a_i\Big)\,{}_p\tilde{F}_q(a + 1; b + 1; z)$$
inside the disc of convergence (`Complex.hasDerivAt_regularizedHGFun`, `Complex.deriv_regularizedHGFun`). The proof is the coefficient identity `Complex.mul_regularizedHGFunCoeff`.

The case $p = 2$, $q = 1$ is the regularized Gauss function `Complex.regularizedGaussHGFun a b c`, the series with parameters $\{a, b\}$ and $\{c\}$. It links to the first module by `Complex.ordinaryHypergeometric_div_Gamma_eq`: if $c$ is not a nonpositive integer, ${}_2F_1(a, b; c; z)/\Gamma(c) = {}_2\tilde{F}_1(a, b; c; z)$. Its radius is at least $1$ for all parameters (`Complex.radius_regularizedGaussHGFunSeries_ge_one`).

#### Bessel functions of the first kind

For complex $a$ and $x$, `Complex.besselJ a x` is
$$J_a(x) = \Big(\frac{x}{2}\Big)^a\,{}_0\tilde{F}_1\Big(;\, a + 1;\, -\frac{x^2}{4}\Big) = \sum_{k \ge 0} \frac{(-1)^k}{k!\,\Gamma(k + a + 1)}\Big(\frac{x}{2}\Big)^{2k + a},$$
by `Complex.besselJ_def`. The power $(x/2)^a$ is the complex power `Complex.cpow`, defined with the principal logarithm of Chapter 1, Section 3. So $J_a$ is analytic on the slit plane (`Complex.analyticOnNhd_besselJ`). For an integer $a$ the power is an integer power, and $J_a$ is entire (`Complex.analyticOnNhd_besselJ_int`). The value at $0$ is $J_0(0) = 1$ and $J_a(0) = 0$ for $a \ne 0$ (`Complex.besselJ_zero`).

**Theorem.** For every integer $n$, $J_{-n}(x) = (-1)^n J_n(x)$.

*Proof.* It suffices to treat $n \ge 0$. The coefficients of ${}_0\tilde{F}_1(;1 - n; z)$ vanish for $k < n$, because $1/\Gamma(1 - n + k) = 0$ there. The remaining coefficients are shifted ones: ${}_0\tilde{F}_1(;1 - n; z) = z^n\,{}_0\tilde{F}_1(;n + 1; z)$ (`Complex.regularizedHGFun_zero_singleton_neg_nat_add_one`). Put $z = -(x/2)^2$. Then
$$J_{-n}(x) = \Big(\frac{x}{2}\Big)^{-n}(-1)^n\Big(\frac{x}{2}\Big)^{2n}{}_0\tilde{F}_1(;n + 1; z) = (-1)^n J_n(x). \qquad \square$$

This is `Complex.besselJ_neg_int`. With `Complex.besselJ_int_neg`, it gives parity: $J_n$ is even for even $n$ and odd for odd $n$ (`Complex.even_besselJ`, `Complex.odd_besselJ`).

**Theorem (Recurrence).** For all complex $a$ and $x$, $2a J_a(x) = x J_{a-1}(x) + x J_{a+1}(x)$.

*Proof sketch.* The contiguous relation `Complex.regularizedHGFun_zero_singleton_eq_mul_add_mul` states
$${}_0\tilde{F}_1(;u; z) = u\,{}_0\tilde{F}_1(;u + 1; z) + z\,{}_0\tilde{F}_1(;u + 2; z).$$
It follows from $1/\Gamma(u + k) = (u + k)/\Gamma(u + k + 1)$ on each coefficient. Put $u = a$ and $z = -(x/2)^2$, and multiply by $(x/2)^{a-1}$. For $x \ne 0$ this gives $J_{a-1} = a(x/2)^{-1}J_a - (x/2)J_{a+1}$. Multiply by $x$. $\square$

This is `Complex.two_mul_self_mul_besselJ`. The derivative formulas follow from the derivative of ${}_0\tilde{F}_1$. On the slit plane, $x J_a'(x) = a J_a(x) - x J_{a+1}(x)$ and $x J_a'(x) = x J_{a-1}(x) - a J_a(x)$ (`Complex.mul_deriv_besselJ_eq_besselJ_add_one`, `Complex.mul_deriv_besselJ_eq_besselJ_sub_one`). Their sum gives $2J_a' = J_{a-1} - J_{a+1}$ (`Complex.two_mul_deriv_besselJ`). The forms with the suffix int hold for all $x$ when $a$ is an integer. The module does not yet prove the Bessel differential equation, the generating function or the integral formulas, and it has no Bessel functions of the second kind.

#### Common errors

1. A learner uses `ordinaryHypergeometric a b c` with $c$ a nonpositive integer and expects a pole or an error. The value is a junk polynomial, because Lean inverts $(c)_n = 0$ to $0$. Use the regularized function, for which these parameters are legitimate.
2. A learner applies `ordinaryHypergeometricSeries_radius_eq_one` without the hypothesis on $c$. The theorem needs that none of $a$, $b$, $c$ is a nonpositive integer. With a nonpositive integer, the series is finite and the radius is `⊤`.
3. A learner applies `Complex.mul_deriv_besselJ_eq_besselJ_add_one` at a negative real $x$ for a noninteger $a$. The power $(x/2)^a$ is not differentiable on the slit. Use the forms with the suffix int for integer orders, which hold everywhere.

### Exercises

1. (A) Show that ${}_2F_1(1, 1; 2; x) = -\log(1 - x)/x$ for $0 < |x| < 1$, by comparing the coefficients.
2. (A) Use `ordinaryHypergeometricSeries_eq_zero_iff` to show that ${}_2F_1(-2, b; c; x)$ is a polynomial of degree at most $2$ in $x$, and compute it.
3. (B) Compute the first three coefficients of $J_0$ and $J_1$, and check $J_0' = -J_1$ with `Complex.two_mul_deriv_besselJ_int` and `Complex.besselJ_neg_int`.
4. (B) Prove `Complex.regularizedHGFunCoeff_add_one` from the functional equation $\Gamma(s + 1) = s\Gamma(s)$ and the recurrence of `ascPochhammer`.
5. (B) Show that $J_{1/2}(x) = \sqrt{2/(\pi x)}\sin x$ for $x > 0$, with the value $\Gamma(3/2) = \sqrt{\pi}/2$ and the duplication formula of Section 2.
6. (C) Prove that $J_a$ satisfies $x^2 J_a'' + x J_a' + (x^2 - a^2) J_a = 0$ on the slit plane, from the two derivative formulas.

### Reference

<?reference?>
