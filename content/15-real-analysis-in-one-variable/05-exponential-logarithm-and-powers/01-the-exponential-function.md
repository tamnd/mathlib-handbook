---
title: The exponential function
kind: theory
modules:
  - Mathlib.Analysis.SpecialFunctions.Exp
  - Mathlib.Analysis.SpecialFunctions.ExpDeriv
  - Mathlib.Analysis.SpecialFunctions.Exponential
explains:
  E3: [Real.hasDerivAt_exp, Real.expOrderIso, Real.exp_eq_exp_ℝ]
  E2: [Real.continuous_exp, Real.deriv_exp, Real.tendsto_exp_atTop, Real.tendsto_exp_atBot, Real.tendsto_exp_div_pow_atTop, Real.range_exp]
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

## The exponential function

### Overview

The exponential function turns sums into products and is its own derivative. The other elementary functions of this volume come from it: the logarithm is its inverse, the real powers are $x^y = \exp(y \log x)$, and the sine and cosine of Chapter 6 come from the complex exponential. This section defines $\exp$ by its power series, proves $\exp(x + y) = \exp(x)\exp(y)$ with the Cauchy product, proves $1 + x \le \exp(x)$, $\exp' = \exp$ and that $\exp$ is a bijection from $\mathbb{R}$ onto $(0, \infty)$. It ends with the decimal value of $e$ and a complete proof of $(1 + 1/n)^n \to e$.

Mathlib defines the exponential on $\mathbb{C}$ first, and the real exponential is the real part.

### Definitions

**Definition (Exponential series).** For $x \in \mathbb{R}$,
$$\exp(x) = \sum_{n=0}^{\infty} \frac{x^n}{n!} = 1 + x + \frac{x^2}{2} + \frac{x^3}{6} + \cdots.$$
The number $e$ is $\exp(1)$.

The series converges absolutely for every $x$. Let $a_n = |x|^n / n!$. For $n \ge 2|x|$ the ratio $a_{n+1}/a_n = |x|/(n+1)$ is at most $1/2$, so after the index $N = \lceil 2|x| \rceil$ the terms are bounded by $a_N 2^{-(n-N)}$. The comparison test of Chapter 1 gives the convergence. The same argument works for complex $z$.

::: mathlib
`Complex.exp` · `Mathlib.Analysis.Complex.Exponential`

Mathlib defines `Complex.exp z` as the limit `(Complex.exp' z).lim`. Here `Complex.exp' z` is the sequence of partial sums $\sum_{m < n} z^m/m!$, packaged as a Cauchy sequence (a `CauSeq`). The proof that it is Cauchy is `Complex.isCauSeq_exp`. This definition needs no theory of infinite sums, only the completeness of $\mathbb{C}$. The defining equation is `Complex.exp_def`.

<?decl Complex.exp?>
:::

::: mathlib
`Real.exp` · `Mathlib.Analysis.Complex.Exponential`

The real exponential is the real part: `Real.exp x = (Complex.exp x).re`. The lemma `Complex.ofReal_exp` says `↑(Real.exp x) = Complex.exp ↑x`, so each identity for `Complex.exp` gives an identity for `Real.exp`. The number $e$ has no name of its own: it is `Real.exp 1`.

<?decl Real.exp?>
:::

::: mathlib
`Real.exp_eq_exp_ℝ` · `Mathlib.Analysis.SpecialFunctions.Exponential`

Mathlib has a second exponential, `NormedSpace.exp`, defined in every complete normed algebra as $\sum_n x^n / n!$. It is the exponential of matrices of Volume 16. The lemma says that on $\mathbb{R}$ the two definitions agree.

<?decl Real.exp_eq_exp_ℝ?>
:::

### Theorems and proofs

**Theorem (Cauchy product).** Let $\sum a_n$ and $\sum b_n$ be absolutely convergent, with sums $A$ and $B$. Let $c_n = \sum_{k=0}^{n} a_k b_{n-k}$. Then $\sum c_n$ converges to $AB$.

*Proof.* Let $A_N$, $B_N$, $C_N$ be the partial sums up to $N$. The sum $C_N$ is the sum of $a_k b_l$ over the pairs with $k + l \le N$, and $A_N B_N$ is the sum over the pairs with $k, l \le N$. So $A_N B_N - C_N$ is the sum over the pairs with $k, l \le N$ and $k + l > N$. In each such pair, $k > N/2$ or $l > N/2$. Let $\alpha = \sum |a_k|$, $\beta = \sum |b_l|$, and let $r_M = \sum_{k > M} |a_k|$ and $s_M = \sum_{l > M} |b_l|$. Then
$$|A_N B_N - C_N| \le r_{\lfloor N/2 \rfloor}\, \beta + \alpha\, s_{\lfloor N/2 \rfloor}.$$
The tails tend to $0$. Since $A_N B_N \to AB$, also $C_N \to AB$. $\square$

**Theorem (Functional equation).** For all real $x$ and $y$, $\exp(x + y) = \exp(x) \exp(y)$, and $\exp(0) = 1$.

*Proof.* The series of $0$ has only the term $1$. Apply the Cauchy product to $a_k = x^k/k!$ and $b_l = y^l/l!$:
$$c_n = \sum_{k=0}^{n} \frac{x^k}{k!} \frac{y^{n-k}}{(n-k)!} = \frac{1}{n!} \sum_{k=0}^{n} \binom{n}{k} x^k y^{n-k} = \frac{(x + y)^n}{n!},$$
by the binomial theorem. So $\exp(x)\exp(y) = \exp(x + y)$. $\square$

::: mathlib
`Real.exp_add` · `Mathlib.Analysis.Complex.Exponential`

Mathlib proves `Complex.exp_add` with the same computation on Cauchy sequences: the lemma `cauchy_product` bounds the difference of the partial sums, and `add_pow` identifies the terms. The real form follows by taking real parts.

<?decl Real.exp_add?>
:::

**Theorem (Order properties).** For every real $x$: (1) $\exp(x) > 0$ and $\exp(-x) = 1/\exp(x)$; (2) $1 + x \le \exp(x)$, with equality only for $x = 0$; (3) $\exp$ is strictly increasing.

*Proof.* (1) $\exp(x)\exp(-x) = \exp(0) = 1$, so $\exp(-x) = 1/\exp(x)$. For $x \ge 0$ every term is nonnegative and the first is $1$, so $\exp(x) \ge 1$. For $x < 0$, $\exp(x) = 1/\exp(-x) > 0$.

(2) For $x > 0$, $\exp(x) \ge 1 + x + x^2/2 > 1 + x$. For $x \le -1$, $1 + x \le 0 < \exp(x)$. Let $-1 < x < 0$ and $t = -x \in (0, 1)$. Since $n! \ge 1$, and $t^2/2 < t^2$,
$$\exp(t) < \sum_{n \ge 0} t^n = \frac{1}{1 - t}.$$
So $\exp(x) = 1/\exp(t) > 1 - t = 1 + x$.

(3) For $x < y$, $\exp(y - x) > 1 + (y - x) > 1$, so $\exp(y) = \exp(x)\exp(y - x) > \exp(x)$. $\square$

::: mathlib
`Real.add_one_le_exp` · `Mathlib.Analysis.Complex.Exponential`

The inequality $x + 1 \le \exp x$ for every real $x$; the strict form for $x \ne 0$ is `Real.add_one_lt_exp`. Positivity is `Real.exp_pos`, and monotonicity is `Real.exp_strictMono`, with the rewriting forms `Real.exp_lt_exp` and `Real.exp_le_exp`. The tactic `positivity` knows that `Real.exp x` is positive.

<?decl Real.add_one_le_exp?>
:::

**Theorem (Derivative of exp).** The function $\exp$ is differentiable everywhere, and $\exp'(x) = \exp(x)$.

*Proof.* For $0 < |h| \le 1$,
$$\left| \exp(h) - 1 - h \right| \le |h|^2 \sum_{n \ge 2} \frac{|h|^{n-2}}{n!} \le |h|^2 \sum_{n \ge 2} \frac{1}{n!} = |h|^2 (e - 2) \le |h|^2.$$
Divide by $|h|$: $\left| (\exp(h) - 1)/h - 1 \right| \le |h|$, so $(\exp(h) - 1)/h \to 1$. For any $x$, by the functional equation,
$$\frac{\exp(x + h) - \exp(x)}{h} = \exp(x) \cdot \frac{\exp(h) - 1}{h} \to \exp(x). \qquad \square$$

The bound needs $|h| \le 1$: for $h = 3$, $\exp(3) - 4 = 16.08\ldots > 9$. A limit needs a bound only near the point. Since $\exp$ is differentiable, it is continuous, and by induction all its derivatives are $\exp$.

::: mathlib
`Real.hasDerivAt_exp` · `Mathlib.Analysis.SpecialFunctions.ExpDeriv`

The statement is `HasDerivAt Real.exp (Real.exp x) x`. Mathlib proves it for `Complex.exp` first and restricts to the reals. The function form is `Real.deriv_exp : deriv Real.exp = Real.exp`. For a composite, `HasDerivAt.exp` turns `HasDerivAt f f' x` into `HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x`.

<?decl Real.hasDerivAt_exp?>
:::

**Theorem (Range of exp).** The exponential is a strictly increasing bijection from $\mathbb{R}$ onto $(0, \infty)$, with $\exp(x) \to +\infty$ as $x \to +\infty$ and $\exp(x) \to 0$ as $x \to -\infty$. For every natural $k$, $\exp(x)/x^k \to +\infty$ as $x \to +\infty$.

*Proof.* For $x \ge 0$, $\exp(x) \ge 1 + x$, so $\exp(x) \to +\infty$ and $\exp(-x) = 1/\exp(x) \to 0$. Injectivity follows from strict monotonicity. Let $c > 0$. Then $\exp(c) > c$, and there is $a < c$ with $\exp(a) < c$. The intermediate value theorem of Chapter 2 on $[a, c]$ gives $x$ with $\exp(x) = c$. For the last claim, $\exp(x) \ge x^{k+1}/(k+1)!$ for $x > 0$, so $\exp(x)/x^k \ge x/(k+1)!$. $\square$

::: mathlib
`Real.expOrderIso` · `Mathlib.Analysis.SpecialFunctions.Exp`

The theorem as one object: an order isomorphism `ℝ ≃o Set.Ioi (0 : ℝ)`. Mathlib defines `Real.log` from its inverse. The limits are `Real.tendsto_exp_atTop`, `Real.tendsto_exp_atBot` (with limit `𝓝 0`) and `Real.tendsto_exp_div_pow_atTop`, in the filter language of Volume 13. The range is `Real.range_exp : Set.range Real.exp = Set.Ioi 0`.

<?decl Real.expOrderIso?>
:::

### Examples

**Example (The decimal value of $e$).** Let $s_N = \sum_{n=0}^{N} 1/n!$. The tail satisfies
$$e - s_N = \frac{1}{(N+1)!}\left(1 + \frac{1}{N+2} + \frac{1}{(N+2)(N+3)} + \cdots \right) < \frac{1}{(N+1)!} \cdot \frac{N+2}{N+1}.$$
For $N = 4$: $s_4 = 65/24 = 2.7083\ldots$ and the tail is less than $0.01$. For $N = 10$: $s_{10} = 2.7182818011\ldots$ and the tail is less than $2.74 \times 10^{-8}$. So $e = 2.718281\ldots$. The same tail bound proves that $e$ is irrational, in Chapter 6. Mathlib proves $2.7182818283 < e < 2.7182818286$ as `Real.exp_one_gt_d9` and `Real.exp_one_lt_d9`, and the coarse bounds `Real.exp_one_gt_two` and `Real.exp_one_lt_three`.

**Example (The limit $(1 + 1/n)^n$).** The claim is $(1 + 1/n)^n \to e$. The values for $n = 1, 10, 100, 1000$ are $2$, $2.59374\ldots$, $2.70481\ldots$, $2.71692\ldots$: the error is about $e/(2n)$.

*Proof.* Let $a_n = (1 + 1/n)^n$. By the binomial theorem,
$$a_n = \sum_{k=0}^{n} \binom{n}{k} \frac{1}{n^k} = \sum_{k=0}^{n} \frac{1}{k!} \prod_{j=0}^{k-1} \left(1 - \frac{j}{n}\right).$$
Each product is in $[0, 1]$, so $a_n \le s_n \le e$. Fix $m$. For $n \ge m$, drop the nonnegative terms with $k > m$:
$$a_n \ge \sum_{k=0}^{m} \frac{1}{k!} \prod_{j=0}^{k-1} \left(1 - \frac{j}{n}\right).$$
This is a finite sum, and each product tends to $1$ as $n \to \infty$. So $\liminf_n a_n \ge s_m$. This holds for every $m$, and $s_m \to e$, so $\liminf_n a_n \ge e$. With $a_n \le e$, this gives $e \le \liminf a_n \le \limsup a_n \le e$, so $a_n \to e$. $\square$

In Mathlib the general form is `Real.tendsto_one_add_div_pow_exp`: for every real $t$, `(1 + t / n) ^ n` tends to `Real.exp t`. Its proof shows $n \log(1 + t/n) \to t$ and uses the continuity of $\exp$.

**Counterexample (Exp of a sum of matrices).** The functional equation uses the binomial theorem, which needs $xy = yx$. Let $X = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ and $Y = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$. Then $X^2 = Y^2 = 0$, so $\exp(X)\exp(Y) = (I + X)(I + Y) = \begin{pmatrix} 2 & 1 \\ 1 & 1 \end{pmatrix}$. But $(X + Y)^2 = I$, so $\exp(X + Y) = \cosh(1) I + \sinh(1)(X + Y)$, with diagonal entries $\cosh 1 \approx 1.543$. So `NormedSpace.exp_add_of_commute` has the hypothesis `Commute x y`.

### The library around it

`Mathlib.Analysis.Complex.Exponential` holds the definition and the algebra (`Real.exp_zero`, `Real.exp_add`, `Real.exp_neg`, `Real.exp_sum`) and the order lemmas. `Mathlib.Analysis.SpecialFunctions.Exp` adds continuity, limits and the comparison with powers. `ExpDeriv` gives the calculus: for `HasDerivAt`, `DifferentiableAt`, `ContDiff` and the others there is a lemma for $\exp$ itself and a lemma for a composite.

Common errors of a learner:

- Expecting a constant `Real.e`. There is none; the number is `Real.exp 1`.
- Mixing `Real.exp` and `NormedSpace.exp`. The bridge is `Real.exp_eq_exp_ℝ`.
- Using the functional equation of the matrix exponential without the hypothesis that the matrices commute.
- Expecting `simp` to prove `Real.exp (Real.log x) = x`. It needs `0 < x`, by `Real.exp_log` of the next section.
- Forgetting the chain rule: for $x \mapsto \exp(2x)$ use `HasDerivAt.exp`, not `Real.hasDerivAt_exp`.

### Exercises

1. (A) Show that $\exp(x) \ge 1 + x + x^2/2$ for $x \ge 0$. Find an $x < 0$ for which it fails.
2. (A) Show that $\exp(nx) = \exp(x)^n$ for every integer $n$. Hint: induction and $\exp(-x) = 1/\exp(x)$.
3. (A) Compute $\lim_{x \to 0} (\exp(3x) - 1)/x$. Hint: the chain rule.
4. (B) Show that $\exp(x) \le 1/(1 - x)$ for $x < 1$. Hint: the case $0 \le x < 1$ is in the proof of the order properties; for $x < 0$ use $1 - x \le \exp(-x)$.
5. (B) Let $f$ be differentiable with $f' = f$ and $f(0) = c$. Show that $f = c \exp$. Hint: differentiate $f(x)\exp(-x)$ and use the mean value theorem.
6. (C) Prove $(1 + t/n)^n \to \exp(t)$ for every real $t \ge 0$ by the method of the example. Hint: the products are now $t^k \prod_j (1 - j/n)/k!$.

### Notes and history

Jacob Bernoulli studied the limit of $(1 + 1/n)^n$ in 1683, in a problem of compound interest. Euler named the number $e$ and gave the series and the limit $\lim (1 + x/n)^n$ in the *Introductio in analysin infinitorum* (1748). The Cauchy product is from Cauchy's *Cours d'analyse* (1821). In Mathlib, the definition through Cauchy sequences goes back to the Lean 3 library, by Chris Hughes and Abhimanyu Pallavi Sudhir.

### Reference

<?reference?>
