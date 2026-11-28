---
title: Variants of the logarithm and the entropy function
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
  - Mathlib.Analysis.SpecialFunctions.BinaryEntropy
  - Mathlib.Analysis.SpecialFunctions.Log.PosLog
  - Mathlib.Analysis.SpecialFunctions.Log.InvLog
  - Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
  - Mathlib.Analysis.SpecialFunctions.Log.Sum
  - Mathlib.Analysis.SpecialFunctions.Log.Summable
  - Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
  - Mathlib.Analysis.SpecialFunctions.Log.ERealExp
  - Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
explains:
  E2: [Real.negMulLog_mul, Real.binEntropy_one_sub, Real.deriv_binEntropy, Real.binEntropy_le_log_two, Real.posLog_mul, Real.abs_log_eq_posLog_add_posLog_inv, Real.sum_log_eq_log_factorial, Real.summable_log_one_add_of_summable, Real.hasProd_of_hasSum_log, ENNReal.log_mul_add]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Variants of the logarithm and the entropy function

### Overview

Section 2 of this chapter treats `Real.log` and its basic identities. Many fields of mathematics use a function that is built from the logarithm and has its own name. Information theory uses $-x \log x$ and the binary entropy $-p \log p - (1 - p)\log(1 - p)$. Complex analysis and number theory use the positive part $\log^+ x = \max(0, \log x)$. Analytic number theory uses $1/\log x$, $\log \log x$ and the sums $\sum_{n \le x} \log n$. Measure theory needs a logarithm on $[0, \infty]$ with the value $-\infty$ at $0$. This section collects these functions.

The modules have a common pattern. Each module defines one function, gives its values at the special points, its continuity and its derivative, and its order properties: monotonicity, convexity and the main inequalities. The proofs reduce to the lemmas of `Real.log` from Section 2, to the derivative rules of Chapter 3 and to the series of Chapter 1. The last part of the section treats infinite products: a product $\prod (1 + a_i)$ converges when $\sum |a_i|$ converges, because the logarithm turns the product into a sum.

### The library around it

#### The function $-x \log x$

The module `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` defines `Real.negMulLog`, the function $x \mapsto -x \log x$. The definition unfolds with `Real.negMulLog_def` or `Real.negMulLog_eq_neg`. The module also has the lemmas for $x \log x$ without the sign, because both forms occur. By the junk value $\log 0 = 0$, the function is $0$ at $0$ (`Real.negMulLog_zero`), and this value is the limit from the right. So `Real.continuous_negMulLog` and `Real.continuous_mul_log` hold on all of $\mathbb{R}$, and `Real.Continuous.mul_log` composes the continuity with a continuous $f$.

The derivative is $\log x + 1$ for $x \log x$ and $-\log x - 1$ for $-x \log x$, at each $x \ne 0$: these are `Real.hasDerivAt_mul_log`, `Real.deriv_mul_log`, `Real.hasDerivAt_negMulLog` and `Real.deriv_negMulLog`. At $0$ the function is not differentiable: `Real.not_DifferentiableAt_log_mul_zero` and `Real.differentiableAt_negMulLog_iff` state this, and `Real.tendsto_deriv_mul_log_atTop` shows that the derivative is unbounded. The second derivative is $1/x$ (`Real.deriv2_mul_log`), so $x \log x$ is convex on $[0, \infty)$: `Real.convexOn_mul_log` and `Real.strictConvexOn_mul_log`. The function `Real.negMulLog` is concave there: `Real.concaveOn_negMulLog` and `Real.strictConcaveOn_negMulLog`. This concavity is the source of the inequalities of entropy.

The sign lemmas follow the sign of $\log x$: `Real.mul_log_nonpos` for $0 \le x \le 1$, `Real.mul_log_nonneg` for $x \ge 1$, and `Real.negMulLog_nonneg`. The basic inequality $\log y \le y - 1$ with $y = 1/x$ gives $x - 1 \le x \log x$ for $x \ge 0$ (`Real.self_sub_one_le_mul_log`), and so $-x \log x \le 1 - x$ (`Real.negMulLog_le_one_sub_self`).

**Theorem.** For all real $x$ and $y$, $-xy\log(xy) = y \cdot (-x\log x) + x \cdot (-y \log y)$.

*Proof.* If $x = 0$ or $y = 0$, both sides are $0$. Otherwise $\log(xy) = \log x + \log y$ by `Real.log_mul`, and the identity follows by distribution. $\square$

This is `Real.negMulLog_mul`. Note that it holds for all reals, also for negative numbers, because `Real.log_mul` only needs $x \ne 0$ and $y \ne 0$.

#### Binary and $q$-ary entropy

The module `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` defines the binary entropy `Real.binEntropy`:
$$h(p) = p \log \tfrac{1}{p} + (1 - p) \log \tfrac{1}{1 - p}.$$
It is the Shannon entropy, in nats, of a coin that shows heads with probability $p$. The lemma `Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub` rewrites it as $\eta(p) + \eta(1 - p)$, with $\eta$ = `Real.negMulLog`, and most proofs start with this rewrite. The $q$-ary entropy `Real.qaryEntropy q p` adds the term $p \log(q - 1)$, and `Real.qaryEntropy_two` shows that the case $q = 2$ is the binary entropy. The definition is total: outside $[0, 1]$ the logarithms take their values at negative numbers, and $h$ is negative there (`Real.binEntropy_neg_of_neg`, `Real.binEntropy_neg_of_one_lt`).

**Theorem.** $h(1 - p) = h(p)$, and for $p \ne 0, 1$ the derivative is $h'(p) = \log(1 - p) - \log p$.

*Proof.* The first claim is clear from the definition: the two terms exchange. For the second, use $h = \eta(p) + \eta(1 - p)$ and the chain rule: $h'(p) = (-\log p - 1) - (-\log(1 - p) - 1) = \log(1 - p) - \log p$. $\square$

These are `Real.binEntropy_one_sub` and `Real.hasDerivAt_binEntropy`. The lemma `Real.deriv_binEntropy` states the formula for `deriv` at every $p$, with no hypothesis. At $p = 0$ and $p = 1$ the function is not differentiable, so `deriv` is $0$ there by convention, and the right side is $0$ too, by the junk value $\log 0 = 0$. The second derivative is $-1/(p(1 - p))$ (`Real.deriv2_binEntropy`), so $h$ is strictly concave on $[0, 1]$ (`Real.strictConcave_binEntropy`).

**Theorem.** $h(p) \le \log 2$ for all real $p$, with equality only at $p = 1/2$.

*Proof sketch.* The derivative $\log(1 - p) - \log p$ is positive on $(0, 1/2)$ and negative on $(1/2, 1)$. So $h$ increases on $[0, 1/2]$ and decreases on $[1/2, 1]$, with maximum $h(1/2) = \log 2$. Outside $[0, 1]$ the function is negative. $\square$

The library splits this into `Real.binEntropy_strictMonoOn`, `Real.binEntropy_strictAntiOn`, `Real.binEntropy_two_inv`, `Real.binEntropy_lt_log_two` and `Real.binEntropy_le_log_two`. The $q$-ary versions have the same names with `qaryEntropy`; the maximum is at $p = 1 - 1/q$ (`Real.qaryEntropy_strictMonoOn`, `Real.qaryEntropy_strictAntiOn`).

#### The positive part of the logarithm

The module `Mathlib.Analysis.SpecialFunctions.Log.PosLog` defines `Real.posLog`, the function $\log^+ x = \max(0, \log x)$ (`Real.posLog_apply`, `Real.posLog_def`). After `open Real` the notation `log⁺ x` is available. The function is even (`Real.posLog_neg`, `Real.posLog_abs`), nonnegative (`Real.posLog_nonneg`), continuous (`Real.continuous_posLog`), and zero exactly on $[-1, 1]$ (`Real.posLog_eq_zero_iff`). For $|x| \ge 1$ it agrees with $\log$ (`Real.posLog_eq_log`).

**Theorem.** For all real $x$, $|\log x| = \log^+ x + \log^+ (1/x)$, and $\log^+(xy) \le \log^+ x + \log^+ y$.

*Proof.* Since $\log(1/x) = -\log x$, one of the two terms $\log^+ x$ and $\log^+(1/x)$ is $|\log x|$ and the other is $0$. For the second claim, if $x = 0$ or $y = 0$ the left side is $0$. Otherwise $\log(xy) = \log x + \log y \le \log^+ x + \log^+ y$, and the right side is also at least $0$. $\square$

These are `Real.abs_log_eq_posLog_add_posLog_inv` and `Real.posLog_mul`. The subadditive bounds follow: `Real.posLog_add` gives $\log^+(x + y) \le \log 2 + \log^+ x + \log^+ y$, and `Real.posLog_sum` and `Real.posLog_norm_sum_le` give the version for a finite sum with $\log$ of the number of terms. These bounds are the form in which $\log^+$ enters the theory of Nevanlinna and of heights.

#### $1/\log x$ and $\log \log x$

The module `Mathlib.Analysis.SpecialFunctions.Log.InvLog` treats the functions $1/\log x$ and $\log \log x$, which appear in the prime number theorem and in Mertens's theorems. The derivatives are
$$\frac{d}{dx} \frac{1}{\log x} = -\frac{1}{x (\log x)^2}, \qquad \frac{d}{dx} \log \log x = \frac{1}{x \log x},$$
at each $x \notin \{-1, 0, 1\}$: `Real.hasDerivAt_inv_log` and `Real.hasDerivAt_log_log`. The points $-1, 0, 1$ are the zeros of $\log$, and the module proves the failure of continuity there, for example `Real.not_continuousAt_inv_log_one` and `Real.not_continuousAt_log_log_one`. The asymptotic lemmas `Real.inv_log_isLittleO_one` and `Real.one_isLittleO_log_log` say that $1/\log x \to 0$ and $\log \log x \to \infty$ in the language of Chapter 7.

#### The logarithm as a limit of powers

The module `Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto` proves the classical limit
$$\lim_{p \to 0^+} \frac{x^p - 1}{p} = \log x \qquad (x > 0).$$
The pointwise form is `tendsto_rpow_sub_one_log`. The form `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log` gives uniform convergence on compact subsets of $(0, \infty)$. Both rest on the explicit error bound `Real.norm_inv_mul_rpow_sub_one_sub_log_le`: if $|p \log x| \le 1$, then $|(x^p - 1)/p - \log x| \le p (\log x)^2$. This bound comes from $x^p = e^{p \log x}$ and the bound $|e^t - 1 - t| \le t^2$ for $|t| \le 1$.

#### Sums of logarithms

The module `Mathlib.Analysis.SpecialFunctions.Log.Sum` compares $\sum_{n \le x} \log n$ with the integral $\int_1^x \log t \, dt = x \log x - x + 1$.

**Theorem.** For every natural number $N$, $\sum_{n=1}^N \log n = \log N!$.

*Proof.* Induction on $N$, with $\log((N+1)!) = \log(N+1) + \log N!$ by `Real.log_mul`. $\square$

This is `Real.sum_log_eq_log_factorial`, with the variant `Real.sum_log_add_one_eq_log_factorial` over `Finset.range`. For real $x \ge 1$, `Real.sum_log_le` and `Real.le_sum_log` give the two bounds $x \log x - x - \log x + 1 \le \sum_{n \le x} \log n \le x \log x - x + \log x + 1$. The lemma `Real.le_sum_log_nat` gives $N \log N - N \le \log N!$, a weak form of Stirling's formula of Chapter 7.

#### Logarithms of series and infinite products

The module `Mathlib.Analysis.SpecialFunctions.Log.Summable` connects summable series with convergent infinite products. Mathlib writes `Multipliable f` for "the product $\prod_i f_i$ converges" and `HasProd f a` for "it converges to $a$", as the analogues of `Summable` and `HasSum`.

**Theorem.** Let $f_i > 0$ and let $\sum_i \log f_i = a$. Then $\prod_i f_i = e^a$.

*Proof.* The exponential is continuous and turns a finite sum into a finite product. So the partial products $\prod_{i \in s} f_i = \exp(\sum_{i \in s} \log f_i)$ tend to $e^a$. $\square$

This is `Real.hasProd_of_hasSum_log`, and `Real.rexp_tsum_eq_tprod` states it with `tsum` and `tprod`. The complex versions are `Complex.hasProd_of_hasSum_log` and `Complex.cexp_tsum_eq_tprod`.

**Theorem.** If $\sum_i a_i$ converges absolutely, then $\sum_i \log(1 + a_i)$ converges.

*Proof sketch.* The terms tend to $0$, so $|a_i| \le 1/2$ for all but finitely many $i$. For $|t| \le 1/2$ the series of the logarithm gives $|\log(1 + t)| \le 2|t|$. The comparison test of Chapter 1 ends the proof. $\square$

This is `Real.summable_log_one_add_of_summable` (for real numbers, summable means absolutely summable), with the complex version `Complex.summable_log_one_add_of_summable`. Together the two theorems give `Real.multipliable_one_add_of_summable`. In a complete normed ring the statement `multipliable_one_add_of_summable` needs only $\sum \|a_i\| < \infty$, and `tprod_one_add_ne_zero_of_summable` shows that the product is not zero when no factor is zero. The finite estimate `Finset.norm_prod_one_add_sub_one_le` states $\|\prod_{i \in t}(1 + a_i) - 1\| \le e^{\sum \|a_i\|} - 1$.

#### The logarithm on $[0, \infty]$

The modules `Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog`, `Mathlib.Analysis.SpecialFunctions.Log.ERealExp` and `Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp` define the logarithm `ENNReal.log` from $[0, \infty]$ to $[-\infty, \infty]$ and the exponential `EReal.exp` back. The values at the ends are the natural ones: `ENNReal.log_zero` gives $\log 0 = -\infty$ and `ENNReal.log_top` gives $\log \infty = \infty$, and on positive finite numbers the function is `Real.log` (`ENNReal.log_pos_real`, `ENNReal.log_ofReal_of_pos`). These functions have no junk values.

**Theorem.** For all $x, y \in [0, \infty]$, $\log(xy) = \log x + \log y$.

*Proof sketch.* For finite positive $x$ and $y$ this is `Real.log_mul`. If $x = 0$, then $xy = 0$ by the convention $0 \cdot \infty = 0$, so the left side is $-\infty$, and the right side is $-\infty$ by the convention $-\infty + a = -\infty$ in `EReal`. The remaining case has $x = \infty$ and $y$ positive, and both sides are $\infty$. $\square$

This is `ENNReal.log_mul_add`. It has no hypothesis, unlike `Real.log_mul`. The same holds for `ENNReal.log_pow`, `ENNReal.log_rpow` and `ENNReal.log_inv`. The function is a strictly monotone bijection (`ENNReal.log_strictMono`, `ENNReal.log_bijective`), and the order lemmas come as iff statements such as `ENNReal.log_le_log_iff` and `ENNReal.zero_le_log_iff`. On the other side, `EReal.exp_add`, `EReal.exp_neg` and `EReal.exp_strictMono` hold. The third module packs both maps into an order isomorphism `ENNReal.logOrderIso` and a homeomorphism `ENNReal.logHomeomorph`, with inverses `EReal.expOrderIso` and `EReal.expHomeomorph`. It proves `ENNReal.exp_log`, `EReal.log_exp`, continuity and measurability (`ENNReal.continuous_log`, `ENNReal.measurable_log`, `Measurable.ennreal_log`), and the formula `ENNReal.rpow_eq_exp_mul_log` for powers.

#### Common errors

1. Forgetting that `Real.binEntropy` and `Real.negMulLog` are defined on all of $\mathbb{R}$. A lemma such as `Real.binEntropy_nonneg` needs $0 \le p \le 1$, and `Real.deriv_binEntropy` holds at $0$ and $1$ only by convention.
2. Expecting `Real.posLog` to vanish only on $(0, 1]$. It is even, so `log⁺ x = 0` holds exactly for $|x| \le 1$, also for negative $x$.
3. Using `Real.log` for a measure or an integral with values in `ENNReal`. The function `ENNReal.log` takes values in `EReal`, and $\log 0 = \bot$, not $0$. A coercion to `ℝ` of this value gives $0$ again.

### Exercises

1. (A) Compute $h(1/4)$ and $h(1/2) - h(1/4)$ in terms of $\log 2$ and $\log 3$, with $h$ = `Real.binEntropy`.
2. (A) Show that $\log^+ (x^n) = n \log^+ x$ for $n \in \mathbb{N}$, and compare with `Real.posLog_pow`.
3. (A) Find the derivative of $x \log \log x$ for $x > 1$ with the rules of `Real.hasDerivAt_log_log`.
4. (B) Show that the $q$-ary entropy has its maximum $\log q$ at $p = 1 - 1/q$. Hint: solve $\log(q - 1) + \log(1 - p) - \log p = 0$.
5. (B) Show that $\prod_{n \ge 2} (1 - 1/n^2)$ converges, and compute its value $1/2$ from the telescoping partial products.
6. (C) Use concavity of $\eta(x) = -x \log x$ and Jensen's inequality to prove that $\sum_{i=1}^n \eta(p_i) \le \log n$ for $p_i \ge 0$ with $\sum p_i = 1$.

### Reference

<?reference?>
