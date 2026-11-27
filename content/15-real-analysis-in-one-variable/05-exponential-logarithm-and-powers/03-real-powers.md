---
title: Real powers
kind: theory
modules:
  - Mathlib.Analysis.SpecialFunctions.Pow.Real
  - Mathlib.Analysis.SpecialFunctions.Pow.Deriv
  - Mathlib.Analysis.SpecialFunctions.Pow.Continuity
  - Mathlib.Analysis.MeanInequalities
explains:
  E3: [Real.rpow, Real.rpow_def_of_pos, Real.rpow_def_of_nonneg, Real.rpow_add, Real.rpow_mul, Real.mul_rpow, Real.hasDerivAt_rpow_const, Real.geom_mean_le_arith_mean_weighted]
  E2: [Real.rpow_def, Real.rpow_def_of_neg, Real.rpow_zero, Real.zero_rpow, Real.rpow_natCast, Real.rpow_add', Real.rpow_neg, Real.rpow_le_rpow, Real.rpow_lt_rpow_left_iff, Real.log_rpow, Real.deriv_rpow_const, Real.hasStrictDerivAt_const_rpow, HasDerivAt.rpow, Real.continuousAt_rpow, Real.young_inequality]
  E1: auto
families: []
requires: [V02, V13, V15.C02, V15.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Real powers

### Overview

Integer powers come from multiplication and rational powers come from roots. A power such as $2^{\sqrt{2}}$ needs a new definition, and the exponential and the logarithm give it in one line: for $x > 0$, $x^y = \exp(y \log x)$. This section proves that the definition agrees with the integer powers, proves the laws of exponents with their exact hypotheses, and computes the derivatives of $x^a$ and $a^x$. The examples find the minimum of $x^x$ and show how the laws fail without their hypotheses. The section ends with the inequality of arithmetic and geometric means.

Mathlib defines $x^y$ for every pair of reals. The values at $x = 0$ follow a convention, and the values for $x < 0$ come from the complex power. These values decide the hypotheses of the laws in the library.

### Definitions

**Definition (Real power).** For $x > 0$ and $y \in \mathbb{R}$, $x^y = \exp(y \log x)$.

So $x^y > 0$, $x^0 = 1$, $x^1 = x$, $1^y = 1$ and $\log(x^y) = y \log x$. The definition agrees with integer powers: $\exp(n t) = \exp(t)^n$ for every integer $n$ by the functional equation, and with $t = \log x$ this is $\exp(n \log x) = x^n$. For a natural number $q \ge 1$, $(x^{1/q})^q = \exp(\log x) = x$, so $x^{1/q}$ is the positive $q$th root. Finally $e^y = \exp(y)$, since $\log e = 1$.

::: mathlib
`Real.rpow` · `Mathlib.Analysis.SpecialFunctions.Pow.Real`

Mathlib defines `Real.rpow x y` as the real part of the complex power: `Real.rpow_def : x ^ y = ((x : ℂ) ^ (y : ℂ)).re`. The complex power is $z^w = \exp(\log z \cdot w)$ with the complex logarithm, with $0^0 = 1$ and $0^w = 0$ for $w \neq 0$. The notation `x ^ y` with `x y : ℝ` means `Real.rpow x y`. One definition through $\mathbb{C}$ gives one theory of powers for $\mathbb{R}$ and $\mathbb{C}$.

<?decl Real.rpow?>
:::

::: mathlib
`Real.rpow_def_of_pos` · `Mathlib.Analysis.SpecialFunctions.Pow.Real`

For a positive base, Mathlib proves the definition of this section: `0 < x → x ^ y = exp (log x * y)`. Most proofs about powers start with a rewrite by this lemma and become proofs about `exp` and `log`. The bridge to natural powers is `Real.rpow_natCast : x ^ (n : ℝ) = x ^ n`, for every base.

<?decl Real.rpow_def_of_pos?>
:::

**Definition (Base $0$ and negative base, Mathlib).** In Mathlib, $0^0 = 1$, $0^y = 0$ for $y \neq 0$, and for $x < 0$, $x^y = \exp(y \log |x|)\cos(\pi y)$.

The convention $0^0 = 1$ agrees with the natural power $x^0 = 1$. The value $0^{-1} = 0$ is a junk value. The formula for $x < 0$ is the real part of the complex power with $\log x = \log|x| + i\pi$. It gives the right value for integer exponents, since $\cos(\pi n) = (-1)^n$, but not the real root: $(-8)^{1/3} = 2\cos(\pi/3) = 1$, not $-2$.

::: mathlib
`Real.rpow_def_of_nonneg` · `Mathlib.Analysis.SpecialFunctions.Pow.Real`

The statement is `0 ≤ x → x ^ y = if x = 0 then (if y = 0 then 1 else 0) else exp (log x * y)`. The special values are `Real.rpow_zero : x ^ 0 = 1`, for every `x`, and `Real.zero_rpow : x ≠ 0 → 0 ^ x = 0`. The negative base is `Real.rpow_def_of_neg : x < 0 → x ^ y = exp (log x * y) * cos (y * π)`.

<?decl Real.rpow_def_of_nonneg?>
:::

### Theorems and proofs

**Theorem (Laws of exponents).** Let $x, u > 0$ and $y, z \in \mathbb{R}$. Then (1) $x^{y+z} = x^y x^z$; (2) $(x^y)^z = x^{yz}$; (3) $(xu)^z = x^z u^z$.

*Proof.* (1) $x^{y+z} = \exp(y\log x + z \log x) = \exp(y \log x)\exp(z \log x)$. (2) Since $x^y > 0$ and $\log(x^y) = y \log x$, $(x^y)^z = \exp(z y \log x) = x^{yz}$. (3) By the functional equation of $\log$, $(xu)^z = \exp(z\log x + z \log u) = x^z u^z$. $\square$

::: mathlib
`Real.rpow_add` · `Mathlib.Analysis.SpecialFunctions.Pow.Real`

The statement is `0 < x → x ^ (y + z) = x ^ y * x ^ z`. The strict hypothesis is necessary, as the counterexample below shows. The variant `Real.rpow_add'` accepts `0 ≤ x` with `y + z ≠ 0`. The form `Real.rpow_neg : 0 ≤ x → x ^ (-y) = (x ^ y)⁻¹` holds at $0$ because $0^{-1} = 0$ in Mathlib.

<?decl Real.rpow_add?>
:::

::: mathlib
`Real.rpow_mul` · `Mathlib.Analysis.SpecialFunctions.Pow.Real`

The statement is `0 ≤ x → x ^ (y * z) = (x ^ y) ^ z`. At $x = 0$ the conventions make both sides agree. For $x < 0$ it fails. The logarithm of a power is `Real.log_rpow : 0 < x → log (x ^ y) = y * log x`.

<?decl Real.rpow_mul?>
:::

::: mathlib
`Real.mul_rpow` · `Mathlib.Analysis.SpecialFunctions.Pow.Real`

The statement is `0 ≤ x → 0 ≤ y → (x * y) ^ z = x ^ z * y ^ z`. Both factors must be nonnegative.

<?decl Real.mul_rpow?>
:::

**Theorem (Monotonicity and continuity).** For $z > 0$, $x \mapsto x^z$ is strictly increasing on $(0, \infty)$. For $a > 1$, $y \mapsto a^y$ is strictly increasing. The map $(x, y) \mapsto x^y$ is continuous on $(0, \infty) \times \mathbb{R}$.

*Proof.* For $0 < x < x'$, $z \log x < z \log x'$, and $\exp$ is increasing. For $y < y'$, $y \log a < y' \log a$ since $\log a > 0$. The map $(x, y) \mapsto y \log x$ is continuous on $(0, \infty) \times \mathbb{R}$, and so is its composite with $\exp$. $\square$

In Mathlib, `Real.rpow_le_rpow : 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z` includes the base $0$, and `Real.rpow_lt_rpow_left_iff` needs `1 < x`. Continuity is `Real.continuousAt_rpow`, at points with `x ≠ 0 ∨ 0 < y`. At $(0, 0)$ the function is not continuous: $x^0 = 1$ for all $x$, but $0^y = 0$ for $y \neq 0$.

**Theorem (Derivatives of powers).** Let $a \in \mathbb{R}$. On $(0, \infty)$, $(x^a)' = a x^{a-1}$. Let $b > 0$. On $\mathbb{R}$, $(b^x)' = b^x \log b$.

*Proof.* By the chain rule and $\log'(x) = 1/x$,
$$\frac{d}{dx}\exp(a \log x) = \exp(a \log x) \cdot \frac{a}{x} = a\, x^a x^{-1} = a\, x^{a-1}.$$
And $\frac{d}{dx}\exp(x \log b) = \exp(x \log b) \log b = b^x \log b$. $\square$

::: mathlib
`Real.hasDerivAt_rpow_const` · `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`

The statement is `x ≠ 0 ∨ 1 ≤ p → HasDerivAt (fun x ↦ x ^ p) (p * x ^ (p - 1)) x`. It holds at negative $x$ too, with the Mathlib values. It holds at $x = 0$ when $p \ge 1$: for $p = 1$ the derivative is $1 \cdot 0^0 = 1$. For $0 < p < 1$ the graph has a vertical tangent at $0$, and the hypothesis excludes that case. The `deriv` form `Real.deriv_rpow_const` has no hypothesis. The derivative of $a^x$ is `Real.hasStrictDerivAt_const_rpow`, for `0 < a`, and the derivative of $f(x)^{g(x)}$ with $f(x) > 0$ is `HasDerivAt.rpow`.

<?decl Real.hasDerivAt_rpow_const?>
:::

**Theorem (Weighted AM-GM inequality).** Let $w_1, \ldots, w_n \ge 0$ with $\sum_i w_i = 1$, and $z_1, \ldots, z_n \ge 0$. Then, with $0^0 = 1$,
$$z_1^{w_1} \cdots z_n^{w_n} \le w_1 z_1 + \cdots + w_n z_n.$$

*Proof.* Let $A = \sum_i w_i z_i$ and $S = \{i : w_i > 0\}$. For $i \notin S$ the factor is $z_i^0 = 1$. If $z_i = 0$ for some $i \in S$, the product is $0 \le A$. Otherwise $z_i > 0$ for $i \in S$, and $A > 0$. The basic inequality $\log t \le t - 1$ with $t = z_i / A$ gives
$$\sum_{i \in S} w_i \log\frac{z_i}{A} \le \sum_{i \in S} w_i \Bigl(\frac{z_i}{A} - 1\Bigr) = 1 - 1 = 0.$$
So $\sum_{i \in S} w_i \log z_i \le \log A$, and applying $\exp$ gives $\prod_{i \in S} z_i^{w_i} \le A$. $\square$

With $w_i = 1/n$ this is $\sqrt[n]{z_1 \cdots z_n} \le \frac{1}{n}(z_1 + \cdots + z_n)$. For example $\sqrt{4 \cdot 9} = 6 \le 6.5$.

::: mathlib
`Real.geom_mean_le_arith_mean_weighted` · `Mathlib.Analysis.MeanInequalities`

For a finite set `s`: if `∀ i ∈ s, 0 ≤ w i`, `∑ i ∈ s, w i = 1` and `∀ i ∈ s, 0 ≤ z i`, then `∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i`. The convention $0^0 = 1$ of Mathlib is the convention of the theorem. The same file proves Young's inequality `Real.young_inequality` and Hölder's inequality from it.

<?decl Real.geom_mean_le_arith_mean_weighted?>
:::

### Examples

**Example (The minimum of $x^x$).** Let $f(x) = x^x = \exp(x \log x)$ for $x > 0$. The claim is that $f$ is strictly decreasing on $(0, 1/e]$, strictly increasing on $[1/e, \infty)$, with minimum $e^{-1/e}$, and that $f(x) \to 1$ as $x \to 0^+$.

*Proof.* By the chain rule and the product rule, $f'(x) = \exp(x \log x)(\log x + 1) = x^x(\log x + 1)$. The factor $x^x$ is positive, and $\log x + 1$ is negative for $x < 1/e$ and positive for $x > 1/e$, since $\log$ is strictly increasing and $\log(1/e) = -1$. Let $0 < x < x' \le 1/e$. The mean value theorem of Chapter 3 gives $c \in (x, x')$ with $f(x') - f(x) = f'(c)(x' - x) < 0$. So $f$ is strictly decreasing on $(0, 1/e]$. The same argument on $[1/e, \infty)$, with $f'(c) > 0$, gives the increase. So the minimum is
$$f(1/e) = \exp\Bigl(\tfrac{1}{e} \cdot (-1)\Bigr) = e^{-1/e} = 0.6922006\ldots, \qquad 1/e = 0.367879\ldots.$$
The previous section proved $x \log x \to 0$ as $x \to 0^+$. Since $\exp$ is continuous at $0$, $x^x \to \exp(0) = 1$. $\square$

The values $0.1^{0.1} = 0.7943\ldots$, $0.01^{0.01} = 0.9550\ldots$ and $0.001^{0.001} = 0.99312\ldots$ show slow convergence. With $0^0 = 1$, the function $x^x$ is continuous on $[0, \infty)$ from the right at $0$. In Mathlib the monotonicity also follows from `Real.mul_log_strictAntiOn` and `Real.mul_log_strictMonoOn`, composed with `Real.exp_strictMono`, after a rewrite with `Real.rpow_def_of_pos`.

**Counterexample (Laws of exponents fail without their hypotheses).** All values are Mathlib values.

- `rpow_add` at $x = 0$: $0^{1 + (-1)} = 0^0 = 1$, but $0^1 \cdot 0^{-1} = 0 \cdot 0 = 0$.
- `rpow_mul` at $x = -1$: $(-1)^{2 \cdot \frac{1}{2}} = -1$, but $((-1)^2)^{1/2} = 1$.
- `mul_rpow` at $x = u = -1$, $z = \frac{1}{2}$: $((-1)(-1))^{1/2} = 1$, but $(-1)^{1/2} = \exp(0)\cos(\pi/2) = 0$, so the product of the factors is $0$.

The second line is the paradox $-1 = (-1)^{2/2} = \sqrt{(-1)^2} = 1$. No definition of $x^y$ for negative $x$ satisfies all three laws.

### The library around it

`Pow.Real` holds the definitions, the special values, the casts, the laws, positivity (`Real.rpow_pos_of_pos`) and the order lemmas. `Pow.Deriv` holds the derivatives and `Pow.Continuity` the continuity. Powers in `NNReal` have their own copy in `Pow.NNReal`, with fewer hypotheses, and the limits are in `Pow.Asymptotics`, which Chapter 7 uses. The tactic `positivity` proves goals `0 < x ^ y` from `0 < x`.

Common errors of a learner:

- Writing `x ^ (1 / 2)` and expecting a square root. The exponent can elaborate as a natural number, and then `1 / 2 = 0` and the result is `1`. Write `x ^ ((1 : ℝ) / 2)` or `Real.sqrt x`.
- Confusing `x ^ (2 : ℕ)` and `x ^ (2 : ℝ)`. They are different functions; `Real.rpow_natCast` converts.
- Using `Real.rpow_add` at a base that can be $0$. Use `Real.rpow_add'` with `y + z ≠ 0`.
- Expecting $(-8)^{1/3} = -2$. In Mathlib the value is $1$.
- Forgetting that the weights of the AM-GM lemma must sum to $1$.

### Exercises

1. (A) Compute $8^{2/3}$, $(1/4)^{-3/2}$ and $e^{2 \log 3}$.
2. (A) Compute the Mathlib values $0^{-2}$, $0^0$, $(-1)^{1/3}$ and $(-4)^{1/2}$. Hint: $\cos(\pi/3) = 1/2$.
3. (A) Find the derivative of $x^{\sqrt{2}}$ on $(0, \infty)$ and of $3^{x^2}$ on $\mathbb{R}$.
4. (B) Prove Bernoulli's inequality $(1 + s)^p \ge 1 + ps$ for $s \ge -1$ and real $p \ge 1$. Hint: $g(s) = (1 + s)^p - 1 - ps$ has $g'(s) = p((1 + s)^{p-1} - 1)$; use the mean value theorem on each side of $0$.
5. (B) Prove Young's inequality $ab \le a^p/p + b^q/q$ for $a, b \ge 0$, $p, q > 1$, $1/p + 1/q = 1$. Hint: AM-GM with weights $1/p$, $1/q$ and $z_1 = a^p$, $z_2 = b^q$.
6. (B) Show that $x^{1/x}$ has its maximum on $(0, \infty)$ at $x = e$. Deduce $e^\pi > \pi^e$.
7. (C) Show that $n(x^{1/n} - 1) \to \log x$ for $x > 0$. Hint: $x^{1/n} = \exp(\log x / n)$ and $(\exp(t) - 1)/t \to 1$.

### Notes and history

The notation $x^{m/n}$ and $x^{-n}$ is due to Wallis and Newton. Euler defined $a^x$ for real $x$ through the exponential and the logarithm in the *Introductio* (1748). The inequality of arithmetic and geometric means for $n$ numbers was proved by Maclaurin (1729) and by Cauchy (1821); see Hardy, Littlewood and Pólya, *Inequalities* (1934), for many proofs. In Mathlib, the real power was defined through the complex power in the Lean 3 library, and its calculus was developed by Sébastien Gouëzel, Yury Kudryashov and others.

### Reference

<?reference?>
