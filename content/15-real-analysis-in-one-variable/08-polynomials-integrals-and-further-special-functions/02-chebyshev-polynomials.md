---
title: Chebyshev polynomials in analysis
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
explains:
  E2: [Polynomial.Chebyshev.T_real_cos, Polynomial.Chebyshev.abs_eval_T_real_le_one, Polynomial.Chebyshev.one_lt_eval_T_real, Polynomial.Chebyshev.roots_T_real, Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one, Polynomial.Chebyshev.integral_measureT_eq_integral_cos, Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne, Polynomial.Chebyshev.integral_eq_sumZeroes]
  E1: auto
families: []
requires: [V06, V18, V15.C03, V15.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Chebyshev polynomials in analysis

### Overview

The Chebyshev polynomials $T_n$ are defined in algebra by a recurrence: $T_0 = 1$, $T_1 = X$ and $T_{n+2} = 2X T_{n+1} - T_n$. Mathlib defines them in `Mathlib.RingTheory.Polynomial.Chebyshev` over every commutative ring, together with the polynomials $U_n$ of the second kind and the rescaled forms $C_n$ and $S_n$. The algebraic file knows nothing about the cosine. This section treats the five modules that connect the polynomials with analysis.

The connection is one identity: $T_n(\cos \theta) = \cos n\theta$. From it the modules derive the classical properties. On $[-1, 1]$ the values of $T_n$ stay in $[-1, 1]$, and outside the interval $|T_n| > 1$. The $n$ roots are $\cos\frac{(2k+1)\pi}{2n}$, and the extrema are at the nodes $\cos\frac{k\pi}{n}$. Among the polynomials of degree at most $n$ bounded by $1$ on $[-1, 1]$, $T_n$ has the largest leading coefficient. The polynomials are orthogonal for the weight $1/\sqrt{1 - x^2}$, and this weight has an exact quadrature rule, the Chebyshev and Gauss rule.

The section uses the cosine and the hyperbolic cosine of Chapter 6, the local extrema of Chapter 3, and the integrals and measures of Volume 18 for the last two modules.

### The library around it

#### The trigonometric identities

In Mathlib the index of a Chebyshev polynomial is an integer: `Polynomial.Chebyshev.T R n` has `n : ℤ`, and $T_{-n} = T_n$ (`Polynomial.Chebyshev.T_neg`). A natural index appears through a cast, as in `T ℝ ↑n`. The algebraic file gives the recurrence `Polynomial.Chebyshev.T_add_two`, the degree `Polynomial.Chebyshev.degree_T` and the leading coefficient $2^{n-1}$ (`Polynomial.Chebyshev.leadingCoeff_T`).

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic` proves the multiple angle formulas. Each comes in four versions: for `Complex.cos`, `Real.cos`, `Complex.cosh` and `Real.cosh`. The name gives the polynomial, the field and the function.

| Lean name | Statement |
|---|---|
| `Polynomial.Chebyshev.T_real_cos` | $T_n(\cos\theta) = \cos n\theta$ |
| `Polynomial.Chebyshev.U_real_cos` | $U_n(\cos\theta)\sin\theta = \sin (n+1)\theta$ |
| `Polynomial.Chebyshev.C_two_mul_real_cos` | $C_n(2\cos\theta) = 2\cos n\theta$ |
| `Polynomial.Chebyshev.S_two_mul_real_cos` | $S_n(2\cos\theta)\sin\theta = \sin (n+1)\theta$ |
| `Polynomial.Chebyshev.T_real_cosh` | $T_n(\cosh\theta) = \cosh n\theta$ |
| `Polynomial.Chebyshev.U_real_cosh` | $U_n(\cosh\theta)\sinh\theta = \sinh (n+1)\theta$ |

The complex versions are `Polynomial.Chebyshev.T_complex_cos`, `Polynomial.Chebyshev.U_complex_cos`, `Polynomial.Chebyshev.T_complex_cosh`, `Polynomial.Chebyshev.C_two_mul_complex_cos` and the others. The formula for $U_n$ is multiplied by $\sin\theta$ and not divided by it, so it holds also where $\sin\theta = 0$. The lemmas `Polynomial.Chebyshev.complex_ofReal_eval_T`, `Polynomial.Chebyshev.complex_ofReal_eval_U`, `Polynomial.Chebyshev.complex_ofReal_eval_C` and `Polynomial.Chebyshev.complex_ofReal_eval_S` move an evaluation at a real point to $\mathbb{C}$. The module proves the complex identities first and deduces the real ones with these lemmas.

**Theorem.** For every integer $n$ and every real $\theta$, $T_n(\cos\theta) = \cos n\theta$.

*Proof.* Since $T_{-n} = T_n$ and $\cos$ is even, take $n \ge 0$. The claim holds for $n = 0$ and $n = 1$. The addition formula gives $\cos (n+2)\theta + \cos n\theta = 2\cos\theta\cos(n+1)\theta$. So the sequence $c_n = \cos n\theta$ satisfies $c_{n+2} = 2\cos\theta\, c_{n+1} - c_n$, the recurrence of $T_n(\cos\theta)$. Induction on $n$ ends the proof. $\square$

#### Values, roots and extrema

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema` describes $T_n$ on the real line.

**Theorem.** If $|x| \le 1$, then $|T_n(x)| \le 1$. If $x > 1$ and $n \ne 0$, then $T_n(x) > 1$.

*Proof.* For $|x| \le 1$ write $x = \cos\theta$ with $\theta = \arccos x$. Then $|T_n(x)| = |\cos n\theta| \le 1$. For $x > 1$ write $x = \cosh t$ with $t > 0$. Then $T_n(x) = \cosh nt$ by `Polynomial.Chebyshev.T_real_cosh`, and $\cosh s > 1$ for $s \neq 0$. $\square$

These are `Polynomial.Chebyshev.abs_eval_T_real_le_one` and `Polynomial.Chebyshev.one_lt_eval_T_real`. The family around them has the forms with $\le$ (`Polynomial.Chebyshev.one_le_eval_T_real`), with the absolute value (`Polynomial.Chebyshev.one_lt_abs_eval_T_real`, `Polynomial.Chebyshev.one_le_abs_eval_T_real`), and for $x < -1$ with the sign $(-1)^n$ (`Polynomial.Chebyshev.one_lt_negOnePow_mul_eval_T_real`). The sign is written with `Int.negOnePow`. The equivalence `Polynomial.Chebyshev.abs_eval_T_real_le_one_iff` combines them: for $n \ne 0$, $|T_n(x)| \le 1$ if and only if $|x| \le 1$. The bound also holds for all derivatives: `Polynomial.Chebyshev.abs_iterate_derivative_T_real_le` states $|T_n^{(k)}(x)| \le T_n^{(k)}(1)$ for $|x| \le 1$, with the iterated derivative written `(⇑Polynomial.derivative)^[k]`.

**Theorem.** For $n \ge 1$, the roots of $T_n$ are the $n$ distinct numbers $\cos\frac{(2k+1)\pi}{2n}$, $0 \le k < n$, each of multiplicity $1$.

*Proof.* $T_n(\cos\theta) = \cos n\theta$ vanishes for $n\theta = (2k+1)\pi/2$. For $0 \le k < n$ the angles $\theta_k = (2k+1)\pi/(2n)$ lie in $(0, \pi)$, where $\cos$ is injective. So these are $n$ distinct roots. A polynomial of degree $n$ has at most $n$ roots with multiplicity. So these are all the roots, and each is simple. $\square$

This is `Polynomial.Chebyshev.roots_T_real`, a statement about the multiset `Polynomial.roots`, with `Polynomial.Chebyshev.roots_T_real_nodup` and `Polynomial.Chebyshev.rootMultiplicity_T_real`. The second kind has `Polynomial.Chebyshev.roots_U_real`, with roots $\cos\frac{(k+1)\pi}{n+1}$. An arithmetic result sits in the same module: `Polynomial.Chebyshev.irrational_of_isRoot_T_real` states that each nonzero real root of $T_n$ is irrational.

The extrema are at the nodes $\cos(k\pi/n)$, where $T_n$ takes the value $(-1)^k$ (`Polynomial.Chebyshev.eval_T_real_cos_int_mul_pi_div`). The module gives the global form on $[-1, 1]$ (`Polynomial.Chebyshev.isMaxOn_T_real` for even $k$, `Polynomial.Chebyshev.isMinOn_T_real` for odd $k$, `Polynomial.Chebyshev.isExtrOn_T_real`), the local form for $0 < k < n$ (`Polynomial.Chebyshev.isLocalMax_T_real`, `Polynomial.Chebyshev.isLocalMin_T_real`), and converses: `Polynomial.Chebyshev.isExtrOn_T_real_iff`, `Polynomial.Chebyshev.isLocalExtr_T_real_iff`, `Polynomial.Chebyshev.eval_T_real_eq_one_iff` and `Polynomial.Chebyshev.eval_T_real_eq_neg_one_iff`.

#### The extremal property

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal` proves Chebyshev's theorem on the leading coefficient. It names the nodes `Polynomial.Chebyshev.node n i`, defined as $\cos(i\pi/n)$, with `Polynomial.Chebyshev.node_eq_one`, `Polynomial.Chebyshev.node_eq_neg_one`, `Polynomial.Chebyshev.node_mem_Icc` and the strict decrease `Polynomial.Chebyshev.strictAntiOn_node`. The value of $T_n$ at the node $i$ is $(-1)^i$ (`Polynomial.Chebyshev.eval_T_real_node`). A linear combination of the values at the nodes is `Polynomial.Chebyshev.sumNodes n c P`, the sum $\sum_{i \le n} P(x_i)\, c_i$.

**Theorem.** Let $P$ be a real polynomial of degree at most $n$ with $|P(x)| \le 1$ on $[-1, 1]$. Then the leading coefficient of $P$ is at most $2^{n-1}$.

*Proof sketch.* If $\deg P = d < n$, the claim for $d$ gives the bound $2^{d-1} \le 2^{n-1}$; so let $\deg P = n$. Lagrange interpolation at the $n + 1$ nodes $x_0 > x_1 > \dots > x_n$ writes the coefficient of $X^n$ as $\sum_i P(x_i)\, c_i$ with $c_i = 1/\prod_{j \ne i}(x_i - x_j)$. Since the nodes decrease, the product has $i$ negative factors, so $(-1)^i c_i > 0$ (`Polynomial.Chebyshev.zero_lt_prod_node_sub_node`). With $|P(x_i)| \le 1$,
$$\sum_i P(x_i)\, c_i \le \sum_i |c_i| = \sum_i (-1)^i c_i = \sum_i T_n(x_i)\, c_i.$$
This is `Polynomial.Chebyshev.sumNodes_le_sumNodes_T`. The right side is the leading coefficient of $T_n$, which is $2^{n-1}$. $\square$

This is `Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one`, and `Polynomial.Chebyshev.coeff_le_of_forall_abs_le_one` states it for the coefficient of degree $n$. For $n \ge 2$ the equality case is `Polynomial.Chebyshev.leadingCoeff_eq_iff_of_forall_abs_le_one`: equality holds only for $P = T_n$. The proof is `Polynomial.Chebyshev.sumNodes_eq_sumNodes_T_iff`: equality forces $P(x_i) = T_n(x_i)$ at all $n + 1$ nodes. The same method bounds the derivatives to the right of the interval: for $x \ge 1$, $P^{(k)}(x) \le T_n^{(k)}(x)$ (`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`), with the equality case `Polynomial.Chebyshev.eval_iterate_derivative_eq_iff_of_bounded` for $0 < k \le n$. For $k = 1$ and $x = 1$ this gives Markov's inequality $|P'(1)| \le n^2$, since $T_n'(1) = n^2$.

#### Orthogonality

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality` defines the measure `Polynomial.Chebyshev.measureT`: the Lebesgue measure with density $1/\sqrt{1 - x^2}$, restricted to $(-1, 1]$. The density is integrable on $[-1, 1]$ (`Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv`), and every function continuous on $[-1, 1]$ is integrable for the measure (`Polynomial.Chebyshev.integrable_measureT`). The lemma `Polynomial.Chebyshev.integral_measureT` writes an integral for the measure as the weighted interval integral.

**Theorem.** For every $f$, $\int f\, d\mu_T = \int_0^\pi f(\cos\theta)\, d\theta$.

*Proof.* Substitute $x = \cos\theta$ in $\int_{-1}^1 f(x)/\sqrt{1 - x^2}\, dx$. Then $dx = -\sin\theta\, d\theta$, and $\sqrt{1 - \cos^2\theta} = \sin\theta$ for $\theta \in [0, \pi]$. The factor $\sin\theta$ cancels, and the minus sign reverses the bounds. $\square$

This is `Polynomial.Chebyshev.integral_measureT_eq_integral_cos`. Orthogonality follows at once.

**Theorem.** For natural numbers $n \ne m$, $\int T_n T_m\, d\mu_T = 0$.

*Proof.* By the previous theorem the integral is $\int_0^\pi \cos n\theta \cos m\theta\, d\theta = \frac12 \int_0^\pi \bigl(\cos(n+m)\theta + \cos(n-m)\theta\bigr)\, d\theta$. For an integer $k \ne 0$, $\int_0^\pi \cos k\theta\, d\theta = \sin(k\pi)/k = 0$. Both $n + m$ and $n - m$ are nonzero. $\square$

The library splits the proof in the same way: `Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT` is the product formula, `Polynomial.Chebyshev.integral_eval_T_real_measureT_of_ne_zero` and `Polynomial.Chebyshev.integral_eval_T_real_measureT_zero` give $0$ and $\pi$, and the result is `Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne`. The norms are `Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero` ($\pi/2$) and `Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero` ($\pi$).

#### The Chebyshev and Gauss quadrature

The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss` defines `Polynomial.Chebyshev.sumZeroes n P`, the value $\frac{\pi}{n} \sum_{i < n} P\bigl(\cos\frac{(2i+1)\pi}{2n}\bigr)$: $\pi$ times the mean of $P$ on the roots of $T_n$. The map is linear (`Polynomial.Chebyshev.sumZeroes_sum`, `Polynomial.Chebyshev.sumZeroes_smul`).

**Theorem.** If $n \ne 0$ and $\deg P < 2n$, then $\int P\, d\mu_T = \frac{\pi}{n} \sum_{i < n} P\bigl(\cos\frac{(2i+1)\pi}{2n}\bigr)$.

*Proof.* Both sides are linear in $P$, and $T_0, \dots, T_{2n-1}$ span the polynomials of degree less than $2n$, since $\deg T_k = k$. So it is enough to take $P = T_k$ with $0 \le k < 2n$. For $k = 0$ both sides are $\pi$ (`Polynomial.Chebyshev.sumZeroes_T_zero`). For $0 < k < 2n$ the integral is $0$ by orthogonality. The sum is $\frac{\pi}{n}\sum_i \cos\frac{k(2i+1)\pi}{2n}$, the real part of a geometric sum with ratio $e^{ik\pi/n} \ne 1$, and a short computation shows that this real part is $0$ when $2n \nmid k$ (`Polynomial.Chebyshev.sumZeroes_T_of_not_dvd`). $\square$

This is `Polynomial.Chebyshev.integral_eq_sumZeroes`. The proof in Mathlib uses the sequence of polynomials `Polynomial.Chebyshev.chebyshevTSequence`, a `Polynomial.Sequence` whose $k$th term has degree $k$, for the spanning step.

#### Common errors

1. Writing `T ℝ n` with `n : ℕ` and expecting a natural index. The index is an integer, so Lean inserts a cast, and a lemma about `T ℝ (n + 2)` matches only after the cast of $n + 2$ is pushed inside.
2. Reading the bound $2^{n-1}$ for $n = 0$ as $1/2$. The exponent is a natural subtraction, so $2^{0-1} = 2^0 = 1$, which is right for the constant polynomials.
3. Using the formula `Polynomial.Chebyshev.U_real_cos` as a formula for $U_n(\cos\theta)$ alone. It holds only after multiplication by $\sin\theta$; to divide, prove $\sin\theta \ne 0$ first.

### Exercises

1. (A) Compute $T_2$, $T_3$ and $T_4$ from the recurrence, and check $T_3(\cos\theta) = \cos 3\theta$ with the triple angle formula.
2. (A) Show that $T_m \circ T_n = T_{mn}$ for natural $m, n$ from $T_n(\cos\theta) = \cos n\theta$ and the fact that two polynomials that agree on $[-1, 1]$ are equal.
3. (B) Show that $\max_{[-1,1]} |P| \ge 2^{1-n}$ for every monic real polynomial $P$ of degree $n \ge 1$, with equality for $2^{1-n} T_n$.
4. (B) Show that $T_n'(1) = n^2$, and deduce from the extremal theorem that $P'(1) \le n^2$ when $\deg P \le n$ and $|P| \le 1$ on $[-1, 1]$.
5. (B) Use the quadrature rule with $n = 2$ to compute $\int_{-1}^1 x^2/\sqrt{1 - x^2}\, dx$, and check the value with the substitution $x = \cos\theta$.
6. (C) Show that no rule $\sum_{i<n} w_i P(y_i)$ with $n$ points can equal $\int P\, d\mu_T$ for all polynomials $P$ of degree $2n$. Hint: apply it to $\prod_{i<n} (X - y_i)^2$.

### Reference

<?reference?>
