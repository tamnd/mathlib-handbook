---
title: The tangent, the inverse functions and bounds for pi
kind: theory
modules:
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
  - Mathlib.Analysis.Real.Pi.Bounds
  - Mathlib.Analysis.Real.Pi.Leibniz
  - Mathlib.Analysis.Real.Pi.Chudnovsky
explains:
  E3: [Real.arctan, Real.arcsin, Real.pi_gt_d2, Real.tendsto_sum_pi_div_four, Real.mul_le_sin]
  E2: [Real.arccos, Real.hasDerivAt_arctan, Real.hasDerivAt_arcsin, Real.arcsin_sin, Real.sin_arcsin, Real.tan_arctan, Real.arctan_tan, Real.hasDerivAt_tan, Real.tan_eq_zero_iff, Real.sqrtTwoAddSeries, Real.cos_pi_over_two_pow, Real.sin_pi_over_two_pow_succ, Real.pi_gt_sqrtTwoAddSeries, Real.pi_lt_sqrtTwoAddSeries, Real.pi_lt_d2, Real.sin_lt, Real.sin_gt_sub_cube]
  E1: auto
families: []
requires: [V02, V13, V15.C02, V15.C03, V15.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The tangent, the inverse functions and bounds for pi

### Overview

The definition of $\pi$ in the previous section gives $2 < \pi < 4$ and no more. This section turns it into digits. The half angle formula expresses $\cos(\pi/2^{n+1})$ by $n$ nested square roots of $2$, and the inequalities $x - x^3/6 < \sin x < x$ trap $\pi$ between two computable numbers. The result is $3.14 < \pi < 3.15$, the bound of Archimedes. Before that the section defines $\tan$, $\arcsin$, $\arccos$ and $\arctan$ and computes their derivatives. The derivative $\arctan' x = 1/(1 + x^2)$ proves the series of Leibniz, $1 - \frac13 + \frac15 - \cdots = \frac{\pi}{4}$. The section ends with Jordan's inequality $\frac{2}{\pi}x \le \sin x$ on $[0, \pi/2]$.

### Definitions

**Definition (Tangent).** For real $x$ with $\cos x \ne 0$, $\tan x = \sin x/\cos x$.

On $(-\pi/2, \pi/2)$ the cosine is positive, so $\tan$ is defined and differentiable there. It has period $\pi$.

::: mathlib
`Real.tan` · `Mathlib.Analysis.Complex.Trigonometric`

`Real.tan` is total, and `Real.tan_eq_sin_div_cos` gives `tan x = sin x / cos x`. At a zero of `cos` the division gives the junk value `0`, so `Real.tan_pi_div_two : tan (π / 2) = 0`. As a consequence `Real.tan_eq_zero_iff` reads `tan θ = 0 ↔ ∃ k : ℤ, k * π / 2 = θ`, with all multiples of `π / 2`.

<?decl Real.tan_eq_zero_iff?>
:::

**Definition (Inverse trigonometric functions).** $\sin$ is a strictly increasing continuous bijection from $[-\pi/2, \pi/2]$ onto $[-1, 1]$, with inverse $\arcsin$. $\cos$ is a strictly decreasing continuous bijection from $[0, \pi]$ onto $[-1, 1]$, with inverse $\arccos$. $\tan$ is a strictly increasing continuous bijection from $(-\pi/2, \pi/2)$ onto $\mathbb{R}$, with inverse $\arctan$.

The claims about $\sin$ and $\cos$ follow from the monotonicity corollary of the previous section and the intermediate value theorem. For $\tan$, the derivative $1/\cos^2 x$ is positive, and $\tan x \to \pm\infty$ as $x \to \pm\pi/2$, since $\sin x \to \pm 1$ and $\cos x \to 0^+$. With these principal branches, $\sin(\arcsin y) = y$ for all $y \in [-1, 1]$, but $\arcsin(\sin x) = x$ only for $x \in [-\pi/2, \pi/2]$. Also $\arccos y = \pi/2 - \arcsin y$, since the right side lies in $[0, \pi]$ and has cosine $y$.

::: mathlib
`Real.arcsin` · `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse`

`Real.arcsin : ℝ → ℝ` is total: Mathlib projects `ℝ` onto `Icc (-1) 1` and applies the inverse of `Real.sinOrderIso`. So `arcsin x = π / 2` for `x ≥ 1`. The inverse laws are `Real.arcsin_sin` (with `-(π / 2) ≤ x` and `x ≤ π / 2`) and `Real.sin_arcsin` (with `-1 ≤ x` and `x ≤ 1`). Mathlib defines `Real.arccos x` as `π / 2 - arcsin x`, the identity above.

<?decl Real.arcsin?>
:::

::: mathlib
`Real.arctan` · `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan`

The inverse of `Real.tanOrderIso : Ioo (-(π / 2)) (π / 2) ≃o ℝ`, followed by the inclusion. No junk value is needed. The laws are `Real.tan_arctan` for all `x` and `Real.arctan_tan` with `-(π / 2) < x` and `x < π / 2`.

<?decl Real.arctan?>
:::

**Definition (Nested square roots).** Put $a_0 = 0$ and $a_{n+1} = \sqrt{2 + a_n}$. By induction $0 \le a_n < 2$.

::: mathlib
`Real.sqrtTwoAddSeries` · `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`

`sqrtTwoAddSeries x 0 = x` and `sqrtTwoAddSeries x (n + 1) = sqrtTwoAddSeries (√(2 + x)) n`: the recursion is on the start value. The numbers $a_n$ are `sqrtTwoAddSeries 0 n`.

<?decl Real.sqrtTwoAddSeries?>
:::

### Theorems and proofs

**Theorem (Derivatives of the inverse functions).** On $(-\pi/2, \pi/2)$, $\tan' x = 1 + \tan^2 x$. For all real $x$, $\arctan' x = 1/(1 + x^2)$. For $-1 < x < 1$, $\arcsin' x = 1/\sqrt{1 - x^2}$ and $\arccos' x = -1/\sqrt{1 - x^2}$.

*Proof.* The quotient rule gives $\tan' x = (\cos^2 x + \sin^2 x)/\cos^2 x = 1 + \tan^2 x$. By the inverse function rule of Chapter 3, at $y = \arctan x$, $\arctan' x = 1/\tan' y = 1/(1 + x^2)$. For $\arcsin$ let $y = \arcsin x \in (-\pi/2, \pi/2)$. Then $\sin' y = \cos y > 0$, and $\cos y = \sqrt{1 - \sin^2 y} = \sqrt{1 - x^2}$. So $\arcsin' x = 1/\sqrt{1 - x^2}$, and $\arccos = \pi/2 - \arcsin$ gives the last formula. $\square$

::: mathlib
`Real.hasDerivAt_arctan` · `Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv`

`HasDerivAt arctan (1 / (1 + x ^ 2)) x`, from `Real.hasDerivAt_tan` by the strict inverse function rule. For `Real.hasDerivAt_arcsin` the hypotheses are `x ≠ -1` and `x ≠ 1`: outside `[-1, 1]` both `arcsin` and `1 / √(1 - x ^ 2)` are junk constants with derivative `0`, so the formula holds there too.

<?decl Real.hasDerivAt_arctan?>
:::

**Lemma (Sine and the line).** For $x > 0$, $x - x^3/6 < \sin x < x$.

*Proof.* Let $g(x) = x - \sin x$. Then $g(0) = 0$ and $g' = 1 - \cos x \ge 0$, with equality only at isolated points, so $g$ is strictly increasing on $[0, \infty)$ and $g(x) > 0$ for $x > 0$. Next let $h(x) = \sin x - x + x^3/6$ and $k = h' = \cos x - 1 + x^2/2$. Then $k(0) = 0$ and $k' = g > 0$ on $(0, \infty)$, so $k > 0$ there. Since $h(0) = 0$ and $h' = k > 0$, $h(x) > 0$ for $x > 0$. $\square$

In Mathlib these are `Real.sin_lt` and `Real.sin_gt_sub_cube`, in `Trigonometric.Bounds`.

**Theorem (Half angles).** For $n \ge 0$, $\cos(\pi/2^{n+1}) = a_n/2$ and $\sin(\pi/2^{n+2}) = \sqrt{2 - a_n}/2$.

*Proof.* For $0 \le y \le \pi$, the double angle formula gives $\cos^2(y/2) = (1 + \cos y)/2$ and $\sin^2(y/2) = (1 - \cos y)/2$, and both $\cos(y/2)$ and $\sin(y/2)$ are nonnegative. Induct on $n$. For $n = 0$, $\cos(\pi/2) = 0 = a_0/2$. If $\cos(\pi/2^{n+1}) = a_n/2$, take $y = \pi/2^{n+1}$: then $2\cos(\pi/2^{n+2}) = \sqrt{2 + a_n} = a_{n+1}$, and $\sin^2(\pi/2^{n+2}) = (2 - a_n)/4$. $\square$

These are `Real.cos_pi_over_two_pow` and `Real.sin_pi_over_two_pow_succ`, in the file `Trigonometric.Basic`.

**Theorem (Bounds for pi).** For $n \ge 0$,
$$2^{n+1}\sqrt{2 - a_n} < \pi < 2^{n+1}\sqrt{2 - a_n} + \frac{1}{4^n}.$$

*Proof.* Put $x = \pi/2^{n+2}$, so $\sin x = \sqrt{2 - a_n}/2$. The lemma gives $\sin x < x$, and multiplication by $2^{n+2}$ gives the lower bound. The lemma also gives $x < \sin x + x^3/6$, so
$$\pi < 2^{n+1}\sqrt{2 - a_n} + \frac{2^{n+2}}{6}\cdot\frac{\pi^3}{2^{3n+6}}.$$
Since $\pi^3 < 64$, the last term is less than $\frac{64}{96 \cdot 4^n} < \frac{1}{4^n}$. $\square$

The lower bound is half the perimeter of the regular polygon with $2^{n+2}$ sides inscribed in the unit circle.

::: mathlib
`Real.pi_gt_sqrtTwoAddSeries` · `Mathlib.Analysis.Real.Pi.Bounds`

`2 ^ (n + 1) * √(2 - sqrtTwoAddSeries 0 n) < π`, and `Real.pi_lt_sqrtTwoAddSeries` with the error `1 / 4 ^ n`. Mathlib does not evaluate the roots in floating point. `Real.pi_lower_bound_start` reduces `a < π` to an upper bound on `sqrtTwoAddSeries 0 n`, and `Real.sqrtTwoAddSeries_step_up` and `Real.sqrtTwoAddSeries_step_down` remove one root at a time with a rational witness, so that each step is an inequality of rationals that `norm_num` checks.

<?decl Real.pi_gt_sqrtTwoAddSeries?>
:::

**Theorem (Leibniz series).** For each $k$,
$$\left| \frac{\pi}{4} - \sum_{i=0}^{k-1} \frac{(-1)^i}{2i + 1} \right| \le \frac{1}{2k + 1}.$$
So the partial sums tend to $\pi/4$.

*Proof.* Since $\tan(\pi/4) = 1$ and $\pi/4 \in (-\pi/2, \pi/2)$, $\arctan 1 = \pi/4$. Fix $k$ and put $R(x) = \arctan x - \sum_{i<k} (-1)^i x^{2i+1}/(2i+1)$. Then $R(0) = 0$, $R(1)$ is the error, and by the finite geometric sum with ratio $-x^2$,
$$R'(x) = \frac{1}{1 + x^2} - \frac{1 - (-x^2)^k}{1 + x^2} = \frac{(-x^2)^k}{1 + x^2}.$$
So $|R'(x)| \le x^{2k}$. Let $u(x) = x^{2k+1}/(2k + 1)$. The functions $u - R$ and $u + R$ have derivatives $x^{2k} \mp R'(x) \ge 0$ and vanish at $0$, so they are nonnegative at $1$. Thus $|R(1)| \le u(1) = 1/(2k + 1)$. $\square$

::: mathlib
`Real.tendsto_sum_pi_div_four` · `Mathlib.Analysis.Real.Pi.Leibniz`

`Tendsto (fun k => ∑ i ∈ range k, (-1) ^ i / (2 * i + 1)) atTop (𝓝 (π / 4))`. The present Mathlib proof uses the power series of `arctan` and Abel's limit theorem. The proof above needs only the mean value theorem and gives an explicit rate, which is slow: $10^6$ terms give about six digits.

<?decl Real.tendsto_sum_pi_div_four?>
:::

**Theorem (Jordan's inequality).** For $0 \le x \le \pi/2$, $\frac{2}{\pi}x \le \sin x \le x$.

*Proof.* The right side is the lemma. Let $g(x) = \sin x - 2x/\pi$, with $g(0) = g(\pi/2) = 0$. Its derivative $\cos x - 2/\pi$ is strictly decreasing, positive at $0$ and negative at $\pi/2$, so it has one zero $x_0$. Then $g$ increases on $[0, x_0]$ and decreases on $[x_0, \pi/2]$. So $g(x) \ge g(0) = 0$ for $x \le x_0$, and $g(x) \ge g(\pi/2) = 0$ for $x \ge x_0$. $\square$

::: mathlib
`Real.mul_le_sin` · `Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds`

`0 ≤ x → x ≤ π / 2 → 2 / π * x ≤ sin x`. The strict form on the open interval is `Real.mul_lt_sin`.

<?decl Real.mul_le_sin?>
:::

### Examples

**Example (Three decimals of pi).** With $\ell_n = 2^{n+1}\sqrt{2 - a_n}$:

| $n$ | $a_n$ | $\ell_n$ | $\ell_n + 4^{-n}$ |
|---|---|---|---|
| 1 | 1.414214 | 3.061467 | 3.311467 |
| 2 | 1.847759 | 3.121445 | 3.183945 |
| 3 | 1.961571 | 3.136548 | 3.152173 |
| 4 | 1.990369 | 3.140331 | 3.144237 |

At $n = 4$, $3.1403 < \pi < 3.1443$, so $3.14 < \pi < 3.15$, from the inscribed polygon with $64$ sides. A proof must not trust calculator decimals. In exact arithmetic one checks $a_4 \le 1.990370$ by squaring, and then $32\sqrt{2 - 1.990370} > 3.14$, that is $1024 \cdot 0.00963 = 9.86112 > 3.14^2 = 9.8596$. These are the integer inequalities that the Mathlib proof checks.

::: mathlib
`Real.pi_gt_d2` · `Mathlib.Analysis.Real.Pi.Bounds`

`3.14 < π`, with a decimal literal. The companion is `Real.pi_lt_d2 : π < 3.15`. The file also has `Real.pi_gt_three`, `Real.pi_gt_d4`, `Real.pi_gt_d6` and `Real.pi_gt_d20`. Each proof is one call of the tactic `pi_lower_bound` or `pi_upper_bound` with a list of rational witnesses.

<?decl Real.pi_gt_d2?>
:::

**Counterexample (The inverse law needs the interval).** $\arctan(\tan \pi) = \arctan 0 = 0 \ne \pi$. In Mathlib also $\arctan(\tan(\pi/2)) = 0 \ne \pi/2$, by the junk value. This is why `Real.arctan_tan` has the hypotheses `-(π / 2) < x` and `x < π / 2`.

### The library around it

Each inverse function has the same API: values (`Real.arcsin_one`, `Real.arctan_one`), range bounds (`Real.arcsin_le_pi_div_two`, `Real.arctan_lt_pi_div_two`), the inverse laws, oddness (`Real.arctan_neg`), continuity, and derivatives in `InverseDeriv` and `ArctanDeriv`. `Real.arctan_add` is the addition formula, and `Real.four_mul_arctan_inv_5_sub_arctan_inv_239` is Machin's formula. The file `Trigonometric.Bounds` collects inequalities such as `Real.lt_tan` and `Real.one_sub_sq_div_two_le_cos`.

The module `Mathlib.Analysis.Real.Pi.Chudnovsky` defines the series of Chudnovsky's formula $\frac{1}{\pi} = \frac{12}{640320^{3/2}} \sum_{n \ge 0} \frac{(-1)^n (6n)!\,(545140134\,n + 13591409)}{(3n)!\,(n!)^3\,640320^{3n}}$. The integer `chudnovskyNum n` is the numerator, the natural number `chudnovskyDenom n` is the denominator, `chudnovskyTerm n` is their quotient in $\mathbb{Q}$, and `chudnovskySum` is the real number on the right side. The module states only the definitions. The identity `chudnovskySum = π⁻¹` is not proved in Mathlib.

Common errors of a learner:

- `Real.arcsin`, `Real.arccos` and `Real.sqrt` are total. A formula with them may hold for a junk reason. Check the hypotheses of a lemma, such as `-1 ≤ x`.
- `tan (π / 2) = 0` in Mathlib. A lemma about `tan` usually needs `cos x ≠ 0`.
- The literal `3.14` is the real number `314 / 100`, and `norm_num` treats it as a rational.
- The Leibniz sum uses `Finset.range k`: it has `k` terms, from `i = 0` to `k - 1`.

### Exercises

1. (A) Compute $\arcsin(1/2)$, $\arccos(-1/2)$ and $\arctan(\sqrt3)$.
2. (A) Prove $\cos(\arctan x) = 1/\sqrt{1 + x^2}$. Hint: $1 + \tan^2 = 1/\cos^2$ and $\cos > 0$ on $(-\pi/2, \pi/2)$.
3. (A) Use the bounds with $n = 2$ to show $\pi > 3.12$.
4. (B) Prove $\arctan x + \arctan y = \arctan\frac{x + y}{1 - xy}$ for $xy < 1$, and deduce Machin's formula $4\arctan\frac15 - \arctan\frac{1}{239} = \frac{\pi}{4}$. Hint: show that the left side lies in $(-\pi/2, \pi/2)$, and compute its tangent.
5. (B) Show that the $k$-th partial sum of the Leibniz series is above $\pi/4$ for odd $k$ and below for even $k$. Hint: the sign of $R'$ is $(-1)^k$.
6. (C) Show that $\pi - 2^{n+1}\sqrt{2 - a_n} < \pi^3/(6 \cdot 4^{n+2})$, and estimate how many square roots give ten digits.

### Notes and history

Archimedes, in *Measurement of a Circle*, used polygons up to $96$ sides and found $3\frac{10}{71} < \pi < 3\frac17$. The series for $\arctan$ and for $\pi/4$ are due to Madhava, and in Europe to Gregory (1671) and Leibniz (1674). Machin computed $100$ digits in 1706 with his formula. The Mathlib files for the bounds and the Leibniz series come from the Lean 3 library.

### Reference

<?reference?>
