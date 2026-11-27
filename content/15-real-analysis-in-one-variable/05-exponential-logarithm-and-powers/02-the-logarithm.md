---
title: The logarithm
kind: theory
modules:
  - Mathlib.Analysis.SpecialFunctions.Log.Basic
  - Mathlib.Analysis.SpecialFunctions.Log.Deriv
  - Mathlib.Analysis.SpecialFunctions.Log.Monotone
  - Mathlib.Analysis.SpecialFunctions.Log.Base
explains:
  E3: [Real.log, Real.exp_log, Real.log_exp, Real.log_mul, Real.hasDerivAt_log, Real.log_le_sub_one_of_pos]
  E2: [Real.log_zero, Real.log_neg_eq_log, Real.exp_log_eq_abs, Real.log_div, Real.log_pow, Real.log_lt_log, Real.strictMonoOn_log, Real.continuousAt_log, Real.deriv_log, Real.tendsto_log_atTop, Real.isLittleO_log_id_atTop, Real.mul_log_strictAntiOn, Real.mul_log_strictMonoOn, Real.logb, Real.rpow_logb]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C02, V15.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The logarithm

### Overview

The previous section proved that $\exp$ is a strictly increasing bijection from $\mathbb{R}$ onto $(0, \infty)$. Its inverse is the natural logarithm. This section proves the properties of $\log$ from the properties of $\exp$: the functional equation $\log(xy) = \log x + \log y$, continuity, the derivative $\log'(x) = 1/x$, the inequality $\log x \le x - 1$, and the slow growth $\log x / x \to 0$. The examples bound the harmonic numbers and find the minimum of $x \log x$.

Mathlib defines `Real.log` on all of $\mathbb{R}$. The extra values are junk values: $\log 0 = 0$ and $\log(-x) = \log x$. They decide the hypotheses of the lemmas.

### Definitions

**Definition (Natural logarithm).** For $x > 0$, $\log x$ is the unique real number $y$ with $\exp(y) = x$.

The number exists because the range of $\exp$ is $(0, \infty)$, and it is unique because $\exp$ is injective. So $\exp(\log x) = x$ for $x > 0$ and $\log(\exp y) = y$ for every $y$. In particular $\log 1 = 0$ and $\log e = 1$.

::: mathlib
`Real.log` · `Mathlib.Analysis.SpecialFunctions.Log.Basic`

Mathlib defines `Real.log x` for every real `x` by `if x = 0 then 0 else expOrderIso.symm ⟨|x|, _⟩`, where `Real.expOrderIso` is $\exp$ as an order isomorphism onto the positive reals. So the value is $\log |x|$ for $x \neq 0$, and $0$ at $0$. A total function is easier to use than a function on a subtype: the term `Real.log x` makes sense for every `x`, and the hypotheses go into the lemmas. The junk values give `Real.log_zero : log 0 = 0` and `Real.log_neg_eq_log : log (-x) = log x`.

<?decl Real.log?>
:::

::: mathlib
`Real.exp_log` · `Mathlib.Analysis.SpecialFunctions.Log.Basic`

The inverse laws are `Real.log_exp : log (exp x) = x`, for every `x`, and `Real.exp_log : 0 < x → exp (log x) = x`. The second needs a hypothesis, because `exp` is positive. For $x \neq 0$ the general form is `Real.exp_log_eq_abs : x ≠ 0 → exp (log x) = |x|`.

<?decl Real.exp_log?>
<?decl Real.log_exp?>
:::

**Definition (Logarithm to a base).** For $b > 0$, $b \neq 1$ and $x > 0$, $\log_b x = \log x / \log b$. In Mathlib this is `Real.logb b x`, with the base first. The inverse law is `Real.rpow_logb : 0 < b → b ≠ 1 → 0 < x → b ^ logb b x = x`, with the real powers of the next section.

### Theorems and proofs

**Theorem (Functional equation).** For $x, y > 0$, $\log(xy) = \log x + \log y$. Consequently $\log(x/y) = \log x - \log y$ and $\log(x^n) = n \log x$ for every integer $n$.

*Proof.* By the functional equation of $\exp$,
$$\exp(\log x + \log y) = \exp(\log x)\exp(\log y) = xy = \exp(\log(xy)).$$
Since $\exp$ is injective, $\log x + \log y = \log(xy)$. Apply this to $x/y$ and $y$ for the quotient. For $n \ge 0$, induction gives $\log(x^n) = n \log x$; for $n = -m$, $\log(x^{-m}) = \log 1 - \log(x^m) = -m \log x$. $\square$

::: mathlib
`Real.log_mul` · `Mathlib.Analysis.SpecialFunctions.Log.Basic`

The statement is `x ≠ 0 → y ≠ 0 → log (x * y) = log x + log y`. The hypothesis is $x \neq 0$, not $x > 0$: since $\log$ is $\log|\cdot|$ away from $0$, the equation holds for negative numbers too. It fails when a factor is $0$, as the counterexample below shows. `Real.log_div` has the same hypotheses. `Real.log_pow` has none, since both sides are $0$ at $x = 0$.

<?decl Real.log_mul?>
:::

**Theorem (Order and continuity).** The logarithm is strictly increasing and continuous on $(0, \infty)$, with $\log x \to +\infty$ as $x \to +\infty$ and $\log x \to -\infty$ as $x \to 0^+$.

*Proof.* Let $0 < x < y$. If $\log x \ge \log y$, then $x = \exp(\log x) \ge \exp(\log y) = y$, a contradiction. For continuity at $x_0 > 0$, let $\varepsilon > 0$ and $\delta = \min(x_0 - x_0 e^{-\varepsilon}, x_0 e^{\varepsilon} - x_0) > 0$. If $|x - x_0| < \delta$, then $x_0 e^{-\varepsilon} < x < x_0 e^{\varepsilon}$, and since $\log$ is increasing, $|\log x - \log x_0| < \varepsilon$. For the limits: if $x > e^M$ then $\log x > M$, and if $0 < x < e^{-M}$ then $\log x < -M$. $\square$

In Mathlib, monotonicity is `Real.strictMonoOn_log` on `Set.Ioi 0`, with the pointwise form `Real.log_lt_log : 0 < x → x < y → log x < log y`. Continuity is `Real.continuousAt_log` at each `x ≠ 0`. The function is not continuous at $0$, because the junk value $0$ is not a limit. The limit at infinity is `Real.tendsto_log_atTop`.

**Theorem (Derivative of log).** For $x > 0$, $\log'(x) = 1/x$.

*Proof.* Let $y = \log x$. For $h \neq 0$ with $x + h > 0$, let $k(h) = \log(x + h) - y$. Then $k(h) \neq 0$ by injectivity, and $k(h) \to 0$ as $h \to 0$ by continuity. From $x + h = \exp(y + k(h)) = x \exp(k(h))$ the increment is $h = x(\exp(k(h)) - 1)$. So
$$\frac{\log(x + h) - \log x}{h} = \frac{1}{x} \cdot \frac{1}{g(k(h))}, \qquad g(k) = \frac{\exp(k) - 1}{k}.$$
By the derivative of $\exp$ at $0$, $g(k) \to 1$ as $k \to 0$ with $k \neq 0$. Since $k(h) \to 0$ and $k(h) \neq 0$, the composition rule of Chapter 2 gives $g(k(h)) \to 1$, and the quotient tends to $1/x$. $\square$

For $x < 0$, the chain rule applied to $\log(-x)$ gives $\frac{1}{-x} \cdot (-1) = \frac{1}{x}$. So $\frac{d}{dx}\log|x| = 1/x$ for every $x \neq 0$.

::: mathlib
`Real.hasDerivAt_log` · `Mathlib.Analysis.SpecialFunctions.Log.Deriv`

The statement is `x ≠ 0 → HasDerivAt log x⁻¹ x`. Mathlib proves it from the derivative of exp with the inverse function rule of Chapter 3 (`HasStrictDerivAt.of_local_left_inverse`), and then uses the even symmetry for negative x. The form `Real.deriv_log : deriv log x = x⁻¹` has no hypothesis: at $0$ both sides are junk values, since `deriv` of a non-differentiable function is $0$ and $0^{-1} = 0$. For a composite use `HasDerivAt.log`, which needs `f x ≠ 0`.

<?decl Real.hasDerivAt_log?>
:::

**Theorem (Basic inequality).** For every $x > 0$,
$$1 - \frac{1}{x} \le \log x \le x - 1,$$
and each inequality is an equality only for $x = 1$.

*Proof.* The previous section proved $1 + t \le \exp(t)$, with equality only for $t = 0$. With $t = \log x$ this is $1 + \log x \le x$, with equality only for $x = 1$. Apply it to $1/x$: $-\log x = \log(1/x) \le 1/x - 1$. $\square$

The graph of $\log$ lies below its tangent line $y = x - 1$ at $1$.

::: mathlib
`Real.log_le_sub_one_of_pos` · `Mathlib.Analysis.SpecialFunctions.Log.Basic`

The statement is `0 < x → log x ≤ x - 1`. The strict form is `Real.log_lt_sub_one_of_pos`, with the extra hypothesis `x ≠ 1`. The next section uses this lemma to prove the inequality of arithmetic and geometric means.

<?decl Real.log_le_sub_one_of_pos?>
:::

**Theorem (Log grows slowly).** As $x \to +\infty$, $\log x / x \to 0$. As $x \to 0^+$, $x \log x \to 0$.

*Proof.* For $x > 1$, the basic inequality for $\sqrt{x}$ gives $\frac{1}{2}\log x \le \sqrt{x} - 1$, so $0 < \log x / x < 2/\sqrt{x} \to 0$. For $0 < x < 1$, put $t = 1/x$: then $x \log x = -\log t / t \to 0$ as $t \to +\infty$. $\square$

In Mathlib the first limit is `Real.isLittleO_log_id_atTop : log =o[atTop] id`, in the language of Chapter 7.

### Examples

**Example (Harmonic numbers).** Let $H_n = 1 + \frac{1}{2} + \cdots + \frac{1}{n}$. Then $\log(n + 1) \le H_n \le 1 + \log n$ for $n \ge 1$. Apply the basic inequality to $x = (k + 1)/k$:
$$\frac{1}{k+1} \le \log(k + 1) - \log k \le \frac{1}{k}.$$
Sum the right inequality over $k = 1, \ldots, n$; the middle telescopes to $\log(n+1)$. Sum the left inequality over $k = 1, \ldots, n - 1$: $H_n - 1 \le \log n$. For $n = 10$: $\log 11 = 2.397895\ldots$, $H_{10} = 2.928968\ldots$, $1 + \log 10 = 3.302585\ldots$. So the harmonic series diverges. The limit of $H_n - \log n$ is the Euler constant $\gamma = 0.5772\ldots$ (Exercise 6).

**Example (The function $x \log x$).** Let $f(x) = x \log x$ for $x > 0$. By the product rule, $f'(x) = \log x + 1$. This is negative for $x < 1/e$ and positive for $x > 1/e$, since $\log(1/e) = -1$. By the mean value theorem, $f$ is strictly decreasing on $(0, 1/e]$ and strictly increasing on $[1/e, \infty)$, with minimum value $f(1/e) = -1/e = -0.367879\ldots$. By slow growth, $f(x) \to 0$ as $x \to 0^+$. In Mathlib, `Real.mul_log_strictAntiOn` gives the decrease on `Set.Icc 0 (exp (-1))` and `Real.mul_log_strictMonoOn` the increase on `Set.Ici (exp (-1))`. The first set includes $0$: the junk value gives $0 \cdot \log 0 = 0$, which is the limit.

**Counterexample (A junk value breaks the functional equation).** In Mathlib, $\log(0 \cdot 2) = \log 0 = 0$, but $\log 0 + \log 2 = 0.693\ldots$. So `Real.log_mul` cannot hold without $x \neq 0$ and $y \neq 0$. For negative numbers it holds: $\log((-2)(-3)) = \log 6 = \log(-2) + \log(-3)$. In a textbook $\log(-2)$ has no meaning; in Mathlib it is $\log 2$.

### The library around it

`Mathlib.Analysis.SpecialFunctions.Log.Basic` holds the definition, the identities, the order lemmas, continuity and limits. `Log.Deriv` holds the derivatives and the power series of the logarithm. `Log.Monotone` holds the monotonicity of $x \log x$ and of $\log x / x$. `Log.Base` holds `Real.logb`. A proof about $\log$ usually goes back to $\exp$: to prove $\log a = b$, prove $\exp b = a$ and rewrite with `Real.log_exp`.

Common errors of a learner:

- Reading `log` as the logarithm to base $10$. `Real.log` is the natural logarithm; base $10$ is `Real.logb 10`.
- Forgetting the hypothesis of `Real.exp_log`. For $x = -2$, `exp (log x)` is $2$.
- Expecting `log` to be continuous at $0$. `Real.continuousAt_log` needs `x ≠ 0`.
- Reading `Real.deriv_log` as a statement that `log` is differentiable at $0$. The equation holds at $0$ only because both sides are junk values.

### Exercises

1. (A) Compute $\log_2 1024$ and $\log_{10} 0.001$, and the Mathlib values $\log(-e)$ and $\log 0$.
2. (A) Find the derivative of $\log(1 + x^2)$ and of $\log(\log x)$ for $x > 1$.
3. (A) Show that $x/(1 + x) \le \log(1 + x) \le x$ for $x > -1$. Hint: the basic inequality for $1 + x$.
4. (B) Show that $\log(1 + x)/x \to 1$ as $x \to 0$, and deduce $(1 + 1/n)^n \to e$. Hint: the derivative of $\log$ at $1$, then the continuity of $\exp$.
5. (B) Show that $\log x / x$ is strictly decreasing on $[e, \infty)$. Deduce $3^\pi > \pi^3$. Hint: for the last claim use $e < 3 < \pi$.
6. (C) Show that $a_n = H_n - \log n$ is decreasing and $b_n = H_n - \log(n + 1)$ is increasing, and that both converge to the same limit $\gamma$, with $1 - \log 2 < \gamma < \frac{3}{2} - \log 2$. Hint: the two bounds of the harmonic example; the bounds on $\gamma$ come from $b_1$ and $a_2$.

### Notes and history

John Napier published the first tables of logarithms in 1614, and Jost Bürgi computed similar tables at about the same time, to turn multiplication into addition. Henry Briggs introduced the base $10$. Euler defined the logarithm as the inverse of the exponential in the *Introductio* (1748). In Mathlib, `Real.log` comes from the Lean 3 library, by Chris Hughes, Abhimanyu Pallavi Sudhir and Jean Lo.

### Reference

<?reference?>
