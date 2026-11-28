---
title: The complex logarithm and the argument
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Complex.Arg
  - Mathlib.Analysis.SpecialFunctions.Complex.Log
  - Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
  - Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
  - Mathlib.Analysis.SpecialFunctions.Complex.Arctan
  - Mathlib.Analysis.SpecialFunctions.Complex.Analytic
  - Mathlib.Analysis.Complex.SqrtDeriv
  - Mathlib.Analysis.Complex.BranchLogRoot
explains:
  E2: [Complex.arg_mul_coe_angle, Complex.log_exp, Complex.exp_log, Complex.log_mul, Complex.hasDerivAt_log, Complex.log_eq_integral, Complex.norm_log_sub_logTaylor_le, Complex.hasSum_arctan, Complex.tendsto_one_add_div_pow_exp]
  E1: auto
families: []
requires: [V15.C05, V15.C06, V17]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The complex logarithm and the argument

### Overview

Section 2 defines the argument of a nonzero complex number and proves the polar form $z = |z| e^{i \arg z}$. The full library of the argument and of the logarithm is in the folder `Mathlib/Analysis/SpecialFunctions/Complex/`. This section goes through it. The argument `Complex.arg` is a real function with values in $(-\pi, \pi]$. The principal logarithm is
$$\log z = \log |z| + i \arg z,$$
the definition of `Complex.log`. Both functions are defined on all of $\mathbb{C}$, with the junk values $\arg 0 = 0$ and $\log 0 = 0$.

The two functions jump on the negative real axis. They are continuous, and the logarithm is holomorphic, on the *slit plane* `Complex.slitPlane`, the set $\mathbb{C} \setminus (-\infty, 0]$. Most theorems of the section have the hypothesis `z ∈ Complex.slitPlane`, and `Complex.mem_slitPlane_iff` states that this means $0 < \operatorname{Re} z$ or $\operatorname{Im} z \ne 0$.

The section then treats the derivative and the power series of the logarithm, explicit bounds for $\log(1 + z)$, the complex arctangent, the square root, and the continuous logarithms and roots on a simply connected set.

### The library around it

#### The argument

The module `Mathlib.Analysis.SpecialFunctions.Complex.Arg` defines `Complex.arg` from the real arcsine: for $\operatorname{Re} x \ge 0$ it is $\arcsin(\operatorname{Im} x / |x|)$, and in the left half-plane the definition adds or subtracts $\pi$. The definition is not the one to use in a proof. The characterizing lemmas are these.

| Lean name | Statement |
|---|---|
| `Complex.arg_mem_Ioc` | $\arg z \in (-\pi, \pi]$ |
| `Complex.range_arg` | the range of $\arg$ is $(-\pi, \pi]$ |
| `Complex.norm_mul_exp_arg_mul_I` | $\lvert x \rvert\, e^{i \arg x} = x$ |
| `Complex.cos_arg` | $\cos \arg x = \operatorname{Re} x / \lvert x \rvert$ for $x \ne 0$ |
| `Complex.sin_arg` | $\sin \arg x = \operatorname{Im} x / \lvert x \rvert$ |
| `Complex.arg_mul_cos_add_sin_mul_I` | $\arg(r(\cos\theta + i \sin\theta)) = \theta$ for $r > 0$, $\theta \in (-\pi, \pi]$ |
| `Complex.ext_norm_arg_iff` | $x = y$ if and only if $\lvert x \rvert = \lvert y \rvert$ and $\arg x = \arg y$ |
| `Complex.arg_exp` | $\arg e^z$ is $\operatorname{Im} z$ reduced into $(-\pi, \pi]$ |

The reduction into $(-\pi, \pi]$ is `toIocMod Real.two_pi_pos (-Real.pi)`. It appears in `Complex.arg_exp`, `Complex.arg_exp_mul_I` and `Complex.arg_cos_add_sin_mul_I_eq_toIocMod`. A second family fixes the value of $\arg$ on the axes and the half-planes: `Complex.arg_eq_zero_iff` ($\operatorname{Re} z \ge 0$ and $\operatorname{Im} z = 0$), `Complex.arg_eq_pi_iff` ($z$ is a negative real), `Complex.arg_nonneg_iff` ($\operatorname{Im} z \ge 0$), `Complex.abs_arg_le_pi_div_two_iff` ($\operatorname{Re} z \ge 0$), and the special values `Complex.arg_one`, `Complex.arg_neg_one`, `Complex.arg_I` and `Complex.arg_neg_I`. Multiplication by a positive real does not change the argument: `Complex.arg_ofReal_mul`, `Complex.arg_mul_ofReal` and the forms for natural numbers.

The argument is not additive. With values in $(-\pi, \pi]$, the sum $\arg x + \arg y$ can leave the interval. The exact rule is a case split.

**Theorem.** Let $x, y \ne 0$. Then $\arg(xy) = \arg x + \arg y + 2\pi k$ with $k = 0$ when $\arg x + \arg y \in (-\pi, \pi]$, $k = 1$ when $\arg x + \arg y \le -\pi$, and $k = -1$ when $\arg x + \arg y > \pi$. In every case $\arg(xy) = \arg x + \arg y$ in the angles $\mathbb{R}/2\pi\mathbb{Z}$.

*Proof.* By the polar form, $xy = |x||y| e^{i(\arg x + \arg y)}$. So $xy$ has the norm $|xy|$ and an argument congruent to $\arg x + \arg y$ modulo $2\pi$. The argument of $xy$ is the unique representative of this class in $(-\pi, \pi]$. The three cases give the three values of $k$, because $\arg x + \arg y \in (-2\pi, 2\pi]$. $\square$

The three cases are `Complex.arg_mul`, `Complex.arg_mul_of_le_neg_pi` and `Complex.arg_mul_of_pi_lt`, and `Complex.arg_mul_eq_add_arg_iff` is the "if and only if" form. The form in the angles is `Complex.arg_mul_coe_angle`, with the coercion `ℝ → Real.Angle`. The angle form has no side condition, and many proofs about the argument are shorter in `Real.Angle`. The family `Complex.arg_coe_angle_eq_iff`, `Complex.arg_inv_coe_angle` and `Complex.arg_neg_coe_angle` translates the other identities. Inverse and conjugation have the same issue at $\pi$: `Complex.arg_inv` and `Complex.arg_conj` state $\arg x^{-1} = -\arg x$ except on the negative real axis, where both are $\pi$.

The argument is continuous on the slit plane (`Complex.continuousOn_arg`, `Complex.continuousAt_arg`). On the negative real axis it has the one-sided limits $\pi$ from above and $-\pi$ from below (`Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero`, `Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero`). As an angle, it is continuous at every nonzero point (`Complex.continuousAt_arg_coe_angle`). The law of cosines in polar form is `Complex.norm_sub_sq_eq_norm_sq_add_norm_sq_sub`: $|a - b|^2 = |a|^2 + |b|^2 - 2|a||b|\cos(\arg a - \arg b)$.

#### The logarithm

The module `Mathlib.Analysis.SpecialFunctions.Complex.Log` defines `Complex.log x` as `Real.log ‖x‖ + arg x * I`. Its real part is `Complex.log_re` and its imaginary part is `Complex.log_im`, so $-\pi < \operatorname{Im} \log x \le \pi$ (`Complex.neg_pi_lt_log_im`, `Complex.log_im_le_pi`).

**Theorem.** For $x \ne 0$, $e^{\log x} = x$. For $z$ with $-\pi < \operatorname{Im} z \le \pi$, $\log e^z = z$.

*Proof.* For the first claim, $e^{\log x} = e^{\log |x|} e^{i \arg x} = |x| e^{i \arg x} = x$ by the polar form. For the second, $|e^z| = e^{\operatorname{Re} z}$, so $\operatorname{Re} \log e^z = \operatorname{Re} z$. The argument of $e^z$ is $\operatorname{Im} z$ reduced into $(-\pi, \pi]$, and the reduction does nothing when $\operatorname{Im} z$ is already in this interval. $\square$

These are `Complex.exp_log` and `Complex.log_exp`. For a general $z$, `Complex.log_exp_exists` gives an integer $n$ with $\log e^z = z + 2\pi i n$, and `Complex.log_exp_eq_sub_toIocDiv` names it. The kernel of $\exp$ is `Complex.exp_eq_one_iff`: $e^x = 1$ if and only if $x \in 2\pi i\mathbb{Z}$. So `Complex.exp_eq_exp_iff_exists_int` describes the fibres of $\exp$, and `Complex.range_exp` states that $\exp$ maps onto $\mathbb{C} \setminus \{0\}$.

The product rule for the logarithm follows from the rule for the argument. `Complex.log_mul` states $\log(xy) = \log x + \log y$ for $x, y \ne 0$ with $\arg x + \arg y \in (-\pi, \pi]$. The cases with a correction $\pm 2\pi i$ are `Complex.log_mul_of_le_neg_pi` and `Complex.log_mul_of_pi_lt`. Multiplication by a positive real is always safe: `Complex.log_ofReal_mul` gives $\log(rx) = \log r + \log x$. The special values are `Complex.log_one`, `Complex.log_neg_one` ($i\pi$), `Complex.log_I` ($i\pi/2$) and `Complex.log_zero`. On the nonnegative reals the complex logarithm agrees with the real one (`Complex.ofReal_log`).

The restriction of $\exp$ to the strip $-\pi < \operatorname{Im} z < \pi$ is a homeomorphism onto the slit plane with inverse $\log$. Mathlib packages it as `Complex.expOpenPartialHomeomorph`, an open partial homeomorphism in the sense of the partial equivalences of Volume 1. The continuity of $\log$ on the slit plane is `continuousAt_clog`, and the composition forms are `ContinuousAt.clog`, `ContinuousOn.clog` and `Filter.Tendsto.clog`. The part clog of these names separates the complex logarithm from `Real.log`.

#### Derivatives and power series

The module `Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv` proves that $\log$ is holomorphic on the slit plane.

**Theorem.** For $z$ in the slit plane, $\log$ has the complex derivative $1/z$ at $z$.

*Proof sketch.* The map $\exp$ has the derivative $e^w \ne 0$ at every $w$, and on the strip it has the continuous inverse $\log$. The inverse function theorem in one variable (Volume 17) then gives the derivative $1/e^{\log z} = 1/z$ for the inverse. The partial homeomorphism `Complex.expOpenPartialHomeomorph` supplies the local inverse. $\square$

This is `Complex.hasDerivAt_log`, with the strict form `Complex.hasStrictDerivAt_log` and the value `Complex.deriv_log`. The library has the usual family of chain rules: `HasDerivAt.clog` gives the derivative $f'/f$ of $\log \circ f$ when $f(x)$ is in the slit plane, and `HasFDerivAt.clog`, `DifferentiableAt.clog` and `Differentiable.clog` are the Fréchet and the qualitative forms. The forms `HasDerivAt.clog_real` treat a curve $f : \mathbb{R} \to \mathbb{C}$. The lemma `Complex.deriv_log_comp_eq_logDeriv` connects with the logarithmic derivative of Chapter 4. The same module proves that $\exp$ is an open map (`Complex.isOpenMap_exp`).

The module `Mathlib.Analysis.SpecialFunctions.Complex.Analytic` proves analyticity: `analyticAt_clog` for $\log$ on the slit plane, and the composition forms `AnalyticAt.clog`, `AnalyticOnNhd.clog`. The complex power $f^g = e^{g \log f}$ is analytic where $f$ takes values in the slit plane (`AnalyticAt.cpow`). The power series at $1$ is `hasFPowerSeriesAt_clog_one`, with the coefficients $(-1)^{n+1}/n$, and `iteratedDeriv_succ_log` computes $\log^{(n+1)}(x) = (-1)^n n!\, x^{-n-1}$. The real logarithm gets the same results: `analyticAt_log` and `hasFPowerSeriesAt_log_one`. The lemmas `AnalyticAt.re_ofReal` and `AnalyticAt.im_ofReal` restrict a complex analytic function to the real line and take its real or imaginary part.

The module `Mathlib.Analysis.Complex.SqrtDeriv` treats `Complex.sqrt`, the square root with $\operatorname{Re} \sqrt z \ge 0$. It is holomorphic on the slit plane with derivative $z^{-1/2}/2$ (`Complex.hasDerivAt_sqrt`, `Complex.differentiableOn_sqrt`), and continuous at every $z$ with $\operatorname{Re} z \ge 0$ or $\operatorname{Im} z \ne 0$ (`Complex.continuousAt_sqrt`).

#### Bounds for the logarithm

The module `Mathlib.Analysis.SpecialFunctions.Complex.LogBounds` gives explicit bounds that a limit argument needs. The Taylor polynomial is `Complex.logTaylor n z`, the sum $\sum_{j < n} (-1)^{j+1} z^j/j$. The term with $j = 0$ is zero, because Mathlib divides by $0$ to get $0$.

**Theorem.** For $1 + z$ in the slit plane,
$$\log(1 + z) = z \int_0^1 \frac{dt}{1 + tz}.$$

*Proof.* Put $g(t) = \log(1 + tz)$ for $t \in [0, 1]$. The segment from $1$ to $1 + z$ stays in the slit plane, because the slit plane is star-shaped about $1$. By the chain rule, $g'(t) = z/(1 + tz)$, and $g(0) = 0$. The fundamental theorem of calculus gives $g(1) = \int_0^1 g'(t)\,dt$. $\square$

This is `Complex.log_eq_integral`. For $|z| < 1$ and $t \in [0, 1]$, the integrand has $|1/(1 + tz)| \le 1/(1 - |z|)$ (`Complex.norm_one_add_mul_inv_le`). The same argument applied to the derivative of $\log(1 + z)$ minus its Taylor polynomial gives the main bound.

**Theorem.** For $|z| < 1$ and every $n$,
$$\Big| \log(1 + z) - \sum_{j=1}^{n} \frac{(-1)^{j+1} z^j}{j} \Big| \le \frac{|z|^{n+1}}{(n+1)(1 - |z|)}.$$

This is `Complex.norm_log_sub_logTaylor_le`. The case $n = 1$ is `Complex.norm_log_one_add_sub_self_le`, and `Complex.norm_log_one_add_half_le_self` gives $|\log(1 + z)| \le \tfrac32 |z|$ for $|z| \le 1/2$. The full Taylor series are `Complex.hasSum_taylorSeries_log` and `Complex.hasSum_taylorSeries_neg_log`, the second one for $-\log(1 - z) = \sum_{n \ge 1} z^n/n$.

The bounds give the classical limit for the exponential.

**Theorem.** For every $t \in \mathbb{C}$, $(1 + t/n)^n \to e^t$ as $n \to \infty$.

*Proof.* For $n > |t|$, $(1 + t/n)^n = e^{n \log(1 + t/n)}$. The bound for $n = 1$ gives $|n \log(1 + t/n) - t| \le n \cdot |t/n|^2 / (2(1 - |t/n|))$, and the right side tends to $0$. So the exponent tends to $t$, and $\exp$ is continuous. $\square$

This is `Complex.tendsto_one_add_div_pow_exp`. The general form `Complex.tendsto_one_add_pow_exp_of_tendsto` only needs $n g(n) \to t$, and `Real.tendsto_one_add_div_pow_exp` is the real version.

#### The arctangent

The module `Mathlib.Analysis.SpecialFunctions.Complex.Arctan` defines
$$\arctan z = -\frac{i}{2} \log \frac{1 + iz}{1 - iz},$$
the definition of `Complex.arctan`. It is a right inverse of $\tan$ away from $\pm i$ (`Complex.tan_arctan`), and a left inverse on the strip $-\pi/2 < \operatorname{Re} z \le \pi/2$ minus the point $\pi/2$ (`Complex.arctan_tan`). It extends the real function (`Complex.ofReal_arctan`).

**Theorem.** For $|z| < 1$, $\arctan z = \sum_{n \ge 0} (-1)^n z^{2n+1}/(2n+1)$.

*Proof.* For $|z| < 1$, both $1 + iz$ and $1 - iz$ have positive real part, so their arguments are in $(-\pi/2, \pi/2)$ (`Complex.arg_one_add_mem_Ioo`). Then the logarithm of the quotient is the difference of the logarithms. Subtract the series of $\log(1 - iz)$ from that of $\log(1 + iz)$. The terms with an even power cancel, and the odd terms give the series after multiplication by $-i/2$. $\square$

This is `Complex.hasSum_arctan`, and `Real.hasSum_arctan` restricts it to the real interval $(-1, 1)$.

#### Continuous logarithms and roots

The module `Mathlib.Analysis.Complex.BranchLogRoot` treats branches on a general space. Let $U$ be an open, simply connected subset of a topological space, and let $g$ be continuous on $U$ with no zero on $U$. Then `Complex.exists_continuousOn_eqOn_exp_comp` gives a continuous $f$ on $U$ with $e^{f} = g$ on $U$. The proof lifts $g$ through the covering map $\exp : \mathbb{C} \to \mathbb{C} \setminus \{0\}$ of the next section. Then $e^{f/n}$ is a continuous $n$-th root of $g$, and `Complex.exists_continuousOn_pow_eq` states this. The version `Complex.UnitDisc.exists_continuousOn_pow_eq` keeps the root inside the unit disc of Chapter 9.

#### Common errors

1. A learner rewrites with `Complex.log_mul` and cannot prove the side condition. The condition $\arg x + \arg y \in (-\pi, \pi]$ is real. When one factor is a positive real, use `Complex.log_ofReal_mul` instead, and for a general identity work in `Real.Angle` with `Complex.arg_mul_coe_angle`.
2. A learner applies `Complex.hasDerivAt_log` at a negative real number. The logarithm is not continuous there. Every derivative lemma for $\log$, $\sqrt{\ }$ and $z^w$ needs `z ∈ Complex.slitPlane`, and `Complex.mem_slitPlane_iff` reduces it to $0 < \operatorname{Re} z \lor \operatorname{Im} z \ne 0$.
3. A learner expects `Complex.log_exp` for every $z$. It needs $-\pi < \operatorname{Im} z \le \pi$. For a general $z$, use `Complex.log_exp_exists` or `Complex.exp_eq_exp_iff_exists_int`.

### Exercises

1. (A) Compute $\log(-1 - i)$ and $\arg(-1 - i)$, and check the result with `Complex.log_re` and `Complex.log_im`.
2. (A) Find $x, y \ne 0$ with $\log(xy) \ne \log x + \log y$, and say which of `Complex.log_mul_of_le_neg_pi` and `Complex.log_mul_of_pi_lt` applies.
3. (B) Prove that $\arg \bar z = -\arg z$ for $z$ not on the negative real axis, from the polar form and `Complex.ext_norm_arg_iff`.
4. (B) Derive the series $-\log(1 - z) = \sum_{n \ge 1} z^n/n$ for $|z| < 1$ from the integral formula `Complex.log_inv_eq_integral` and the geometric series.
5. (B) Prove that $\log$ is the unique continuous function $L$ on the slit plane with $e^{L(z)} = z$ and $L(1) = 0$. Hint: $L - \log$ is continuous with values in $2\pi i \mathbb{Z}$, and the slit plane is connected.
6. (C) Prove that no continuous function $L$ on $\mathbb{C} \setminus \{0\}$ satisfies $e^{L(z)} = z$. Hint: integrate $L'$ along the unit circle, or follow $\operatorname{Im} L(e^{i\theta})$ for $\theta \in [0, 2\pi]$.

### Reference

<?reference?>
