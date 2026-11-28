---
title: Value distribution theory
kind: api
modules:
  - Mathlib.Analysis.Complex.CanonicalDecomposition
  - Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
  - Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Truncated
  - Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Asymptotic
  - Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
  - Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation
  - Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
  - Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
  - Mathlib.Analysis.Complex.ValueDistribution.Cartan
  - Mathlib.Analysis.Complex.ValueDistribution.SecondMainTheorem
explains:
  E2: [Complex.canonicalFactor, Complex.norm_canonicalFactor_eval_circle_eq_one, MeromorphicOn.exists_canonicalDecomp, ValueDistribution.logCounting, ValueDistribution.proximity, ValueDistribution.characteristic, ValueDistribution.characteristic_sub_characteristic_inv, ValueDistribution.abs_characteristic_sub_characteristic_shift_le, ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage, ValueDistribution.characteristic_monotoneOn]
  E1: auto
families: []
requires: [V19.C02, V19.C03, V18.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Value distribution theory

### Overview

A nonconstant polynomial of degree $d$ takes every value $a \in \mathbb{C}$ exactly $d$ times, with multiplicity. Value distribution theory, also called Nevanlinna theory, asks the same question for a meromorphic function $f$ on all of $\mathbb{C}$. Such a function can take a value infinitely often, so the theory counts the solutions of $f(z) = a$ in the disc $|z| \le r$ and studies the growth of the count as $r \to \infty$.

The theory uses three functions of $r$, each defined for a value $a$ in $\mathbb{C} \cup \{\infty\}$.

1. The logarithmic counting function $N(r, a)$ counts the solutions of $f(z) = a$ in $|z| \le r$, with a logarithmic weight. For $a = \infty$ it counts the poles.
2. The proximity function $m(r, a)$ measures how close $f$ is to $a$ on the circle $|z| = r$, on average.
3. The characteristic function $T(r, a) = m(r, a) + N(r, a)$.

The first main theorem states that $T(r, a)$ and $T(r, \infty)$ differ by a bounded function. So $T(r, \infty)$ is a single measure of the growth of $f$, and for every $a$ the sum $m(r, a) + N(r, a)$ is equal to it, up to a bounded error. A value that $f$ takes rarely must be one that $f$ approaches closely on the circles.

This section describes the Mathlib form of these functions and theorems. It uses the divisor, the trailing coefficient and Jensen's formula of Section 2, and the circle average `Real.circleAverage` of Volume 18.

### The library around it

#### Canonical factors

The module `Mathlib.Analysis.Complex.CanonicalDecomposition` refines the factorization of Section 2 on a disc. Section 2 writes a meromorphic function on the closed disc $\overline{B}(0, R)$ as $\prod_u (z - u)^{d(u)} g(z)$, with $g$ analytic and free of zeros. The canonical decomposition replaces the factor $z - u$ by a factor of norm $1$ on the boundary circle. For $|w| < R$, the canonical factor `Complex.canonicalFactor R w` is
$$B_{R,w}(z) = \frac{R^2 - \overline{w} z}{R(z - w)},$$
by `Complex.canonicalFactor_apply`. It has a simple pole at $w$ (`Complex.divisor_canonicalFactor`) and no zero in the open disc. Its inverse is the Blaschke factor of the disc.

**Theorem.** If $|w| < R$ and $|z| = R$, then $|B_{R,w}(z)| = 1$.

*Proof.* Since $|z| = R$, $R^2 = z\overline{z}$. So $R^2 - \overline{w}z = z(\overline{z} - \overline{w})$, and its norm is $R|z - w|$. Divide by the norm $R|z - w|$ of the denominator. $\square$

This is `Complex.norm_canonicalFactor_eval_circle_eq_one`. The structure `Complex.CanonicalDecomp f g R` records a canonical decomposition: $f$ is meromorphic on the closed disc, $g$ is in normal form and has no zero in the open disc, and $f$ equals $\prod_u B_{R,u}^{-d(u)} \cdot g$ off a discrete set, where $d$ is the divisor of $f$ on the open disc. `MeromorphicOn.exists_canonicalDecomp` proves that a decomposition exists when $f$ is not zero near any point of the closed disc. The extended form `Complex.ECanonicalDecomp` also takes out the zeros and poles on the boundary circle, with the factors $(z - u)^{d(u)}$ of Section 2. Then $g$ is analytic and free of zeros on the closed disc (`MeromorphicOn.exists_ecanonicalDecomp`), and `Complex.ECanonicalDecomp.log_norm_eq` gives $\log|g(w)|$ as a finite sum. Since the canonical factors have norm $1$ on the circle, $\log|f|$ and $\log|g|$ have the same average on the circle, up to the boundary factors. This is a second proof of Jensen's formula, and the integral presentation of the proximity function below uses the same idea.

#### The logarithmic counting function

The counting function starts from a divisor. For a function $D$ with locally finite support on a proper normed space, `Function.locallyFinsuppWithin.logCounting D` is the function
$$r \mapsto \sum_{0 < |z| \le r} D(z) \log\frac{r}{|z|} + D(0) \log r.$$
It is an additive map from divisors to functions of $r$. For one point, `Function.locallyFinsuppWithin.logCounting_single_eq_log_sub_const` computes the value $n(\log r - \log|e|)$ when $|e| \le r$. So one point gives growth $\log r$, and the function is unbounded (`Function.locallyFinsuppWithin.one_isLittleO_logCounting_single`).

For a meromorphic function $f : 𝕜 \to E$ and a value `a : WithTop E`, `ValueDistribution.logCounting f a` applies this map to a part of a divisor.

1. For $a = \top$, which plays the role of $\infty$, it uses the negative part of the divisor of $f$, the poles (`ValueDistribution.logCounting_top`).
2. For a finite value $a_0$, it uses the positive part of the divisor of $f - a_0$, the solutions of $f(z) = a_0$ (`ValueDistribution.logCounting_coe`).

The function is nonnegative for $r \ge 1$, is $0$ at $r = 0$ (`ValueDistribution.logCounting_eval_zero`) and is monotone on $(0, \infty)$ (`ValueDistribution.logCounting_monotoneOn`). The value $0$ of $f$ is the value $\top$ of $1/f$ (`ValueDistribution.logCounting_inv`). Poles of a sum or product come from poles of the factors, so `ValueDistribution.logCounting_add_top_le` and `ValueDistribution.logCounting_mul_top_le` bound the counting function of a sum or product for $r \ge 1$. In the complex case, Jensen's formula of Section 2 takes this form.

**Theorem.** For $f$ meromorphic on $\mathbb{C}$ and $R \ne 0$,
$$N(R, 0) - N(R, \infty) = \frac{1}{2\pi}\int_0^{2\pi} \log|f(Re^{i\theta})|\,d\theta - \log|c_f|,$$
where $c_f$ is the trailing coefficient of $f$ at $0$.

This is `ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const`. The left side is the counting function of the full divisor (`ValueDistribution.log_counting_zero_sub_logCounting_top`).

The module `Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Asymptotic` reads properties of $f$ from the growth of $N(r, \infty)$. The function is bounded if and only if $f$ has no poles, that is, its normal form is entire (`ValueDistribution.logCounting_isBigO_one_iff_analyticOnNhd`). It is $O(\log r)$ if and only if $f$ has finitely many poles (`ValueDistribution.logCounting_isBigO_log_iff_finite_support`).

The truncated counting function `ValueDistribution.truncatedLogCounting f a` counts each solution of $f(z) = a$ once, without multiplicity. It is the counting function of the divisor cut to the values $0$ and $1$, and it is at most `ValueDistribution.logCounting f a` for $r \ge 1$ (`ValueDistribution.truncatedLogCounting_le`). The second main theorem uses it.

#### The proximity function

For $f : \mathbb{C} \to E$, `ValueDistribution.proximity f a` is the circle average of
$$\log^+ |f| \text{ for } a = \infty, \qquad \log^+ \frac{1}{|f - a_0|} \text{ for } a = a_0,$$
where $\log^+ x = \max(0, \log x)$ is `Real.posLog` (`ValueDistribution.proximity_top`, `ValueDistribution.proximity_coe`). The value $m(r, \infty)$ is large when $|f|$ is large on much of the circle, and $m(r, a_0)$ is large when $f$ is close to $a_0$ on much of the circle. The value $0$ of $f$ is the value $\infty$ of $1/f$ (`ValueDistribution.proximity_inv`). Since $\log^+(x + y) \le \log^+ x + \log^+ y + \log 2$, `ValueDistribution.proximity_add_top_le` bounds the proximity of a sum.

The identity $\log^+ x - \log^+ (1/x) = \log x$ for $x > 0$ gives
$$m(r, \infty, f) - m(r, \infty, 1/f) = \frac{1}{2\pi}\int_0^{2\pi} \log|f(re^{i\theta})|\,d\theta,$$
which is `ValueDistribution.proximity_sub_proximity_inv_eq_circleAverage`.

The module `Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation` writes $m(r, \infty)$ as an iterated circle average. For every $R$, the average over $|a| = 1$ of the average of $\log|f - a|$ on the circle of radius $R$ is the proximity function (`ValueDistribution.circleAverage_circleAverage_eq_proximity_top`). The proof uses the identity $\frac{1}{2\pi}\int_0^{2\pi} \log|w - e^{i\alpha}|\,d\alpha = \log^+|w|$ and Fubini's theorem. The integrand is `ValueDistribution.Cartan.cartanKernel f R α β`, the value $\log|f(Re^{i\beta}) - e^{i\alpha}|$, and the lemmas `ValueDistribution.Cartan.integrable_integral_norm_cartanKernel` and `ValueDistribution.Cartan.integrableOn_cartanKernel_left` give the integrability that Fubini's theorem needs.

#### The characteristic function and the first main theorem

The characteristic function `ValueDistribution.characteristic f a` is the sum `proximity f a + logCounting f a`. For a constant $c$ it is the constant $\log^+|c|$ (`ValueDistribution.characteristic_const`). It is subadditive up to $\log 2$ for sums (`ValueDistribution.characteristic_add_top_le`), subadditive for products (`ValueDistribution.characteristic_mul_top_le`), and multiplied by $n$ for an $n$-th power (`ValueDistribution.characteristic_pow_top`).

**Theorem (First main theorem, part 1).** For $f : \mathbb{C} \to \mathbb{C}$ meromorphic, $T(r, \infty, f) - T(r, \infty, 1/f)$ is bounded.

*Proof.* The difference of the proximity terms is the circle average of $\log|f|$, by the identity above. The poles of $1/f$ are the zeros of $f$, so the difference of the counting terms is minus the counting function of the full divisor of $f$. By Jensen's formula in the form above, the sum is the constant $\log|c_f|$ for $r \ne 0$. $\square$

The exact formula is `ValueDistribution.characteristic_sub_characteristic_inv`, and `ValueDistribution.characteristic_sub_characteristic_inv_le` gives an explicit bound for all $r$. Since $T(r, \infty, 1/f)$ is $T(r, 0, f)$, the theorem compares the values $0$ and $\infty$.

**Theorem (First main theorem, part 2).** For $f$ meromorphic with values in $E$ and $a_0 \in E$,
$$|T(r, \infty, f) - T(r, \infty, f - a_0)| \le \log^+|a_0| + \log 2.$$

*Proof.* The functions $f$ and $f - a_0$ have the same poles with the same orders, so the counting terms are equal. For the proximity terms, $\log^+|f - a_0| \le \log^+|f| + \log^+|a_0| + \log 2$, and the same bound holds with $f$ and $f - a_0$ exchanged. Average on the circle. $\square$

This is `ValueDistribution.abs_characteristic_sub_characteristic_shift_le`, and `ValueDistribution.isBigO_characteristic_sub_characteristic_shift` is its asymptotic form. The two parts combine. For a Möbius transformation $w \mapsto (aw + b)/(cw + d)$ with $ad - bc \ne 0$, the characteristic function of the composite differs from that of $f$ by a bounded function (`ValueDistribution.isBigO_characteristic_sub_characteristic_moebius`).

#### Cartan's formula and monotonicity

**Theorem (Cartan's formula).** For $f$ meromorphic on $\mathbb{C}$ and $R \ne 0$,
$$T(R, \infty) = \frac{1}{2\pi}\int_0^{2\pi} N(R, e^{i\alpha})\,d\alpha + \frac{1}{2\pi}\int_0^{2\pi} \log|c_{f - e^{i\alpha}}|\,d\alpha,$$
where $c_{f-a}$ is the trailing coefficient of $f - a$ at $0$.

*Proof sketch.* Apply Jensen's formula to $f - a$ for each $a$ with $|a| = 1$. This writes the circle average of $\log|f - a|$ as $N(R, a) - N(R, \infty) + \log|c_{f-a}|$. Average over $a$. The left side becomes $m(R, \infty)$ by the integral presentation, and $N(R, \infty)$ does not depend on $a$. Move it to the left side. $\square$

This is `ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage`. The second term does not depend on $R$, and the first term is an average of the monotone functions $N(R, e^{i\alpha})$. So the characteristic function is monotone on $(0, \infty)$, `ValueDistribution.characteristic_monotoneOn`. The definition as $m + N$ does not show this, because $m(r, \infty)$ need not be monotone.

#### The second main theorem

The second main theorem bounds the sum of $m(r, a_j)$ over $q$ distinct values by $2T(r, \infty)$ plus an error term. A corollary is Picard's theorem: a nonconstant meromorphic function omits at most two values of $\mathbb{C} \cup \{\infty\}$. The module `Mathlib.Analysis.Complex.ValueDistribution.SecondMainTheorem` does not prove it at this commit. It holds a preparatory inequality, `Real.exists_sum_posLog_inv_norm_sub_le`: for a finite set $s$ of points of a normed field, a constant $C$ exists with
$$\sum_{a \in s} \log^+\frac{1}{|w - a|} \le \log^+\Big|\sum_{a \in s} \frac{1}{w - a}\Big| + C$$
for all $w$. It reduces the proximity to several values to one term.

#### Common errors

1. A learner reads `ValueDistribution.logCounting f 0` as the count of the poles. The value $0$ counts the zeros, and the poles are `ValueDistribution.logCounting f ⊤`. The second argument has type `WithTop E`, and `⊤` is the value $\infty$.
2. A learner expects `ValueDistribution.characteristic f a` to be monotone from its definition, or tries to prove the first main theorem for $T(r, a)$ with finite $a$ directly. Mathlib states both theorems for the value `⊤` and moves other values to `⊤` with $1/(f - a)$ and the shift.
3. A learner applies the first main theorem to a function that is only meromorphic on a disc. The theorems need `Meromorphic f`, that is, meromorphic at every point of $\mathbb{C}$, because $r$ runs to infinity.

### Exercises

1. (A) Compute `ValueDistribution.logCounting f ⊤` for $f(z) = 1/z$, and check that it is $O(\log r)$, as `ValueDistribution.logCounting_isBigO_log_iff_finite_support` predicts.
2. (A) Prove $\log^+ x - \log^+(1/x) = \log x$ for $x > 0$, and derive `ValueDistribution.proximity_sub_proximity_inv_eq_circleAverage` from it.
3. (B) For $f(z) = e^z$, show that $N(r, \infty) = N(r, 0) = 0$, that $m(r, \infty) = r/\pi$, and that $T(r, \infty) = r/\pi$.
4. (B) Show that $|B_{R,w}(z)| > 1$ for $|z| < R$, $z \ne w$, with the maximum principle and `Complex.norm_canonicalFactor_eval_circle_eq_one`.
5. (B) For a polynomial $p$ of degree $d \ge 1$, show that $T(r, \infty) = d \log r + O(1)$.
6. (C) Use the first main theorem to show that if $f$ is meromorphic and nonconstant and $T(r, \infty)$ is unbounded, then for every $a \in \mathbb{C}$ either $f$ takes the value $a$ or $m(r, a)$ is unbounded.

### Reference

<?reference?>
