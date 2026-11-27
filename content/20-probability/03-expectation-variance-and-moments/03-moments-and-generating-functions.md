---
title: Moments and generating functions
kind: theory
modules:
  - Mathlib.Probability.Moments.Basic
  - Mathlib.Probability.Moments.IntegrableExpMul
  - Mathlib.Probability.Moments.MGFAnalytic
  - Mathlib.Probability.Moments.ComplexMGF
  - Mathlib.Probability.Moments.SubGaussian
  - Mathlib.Probability.Moments.Tilted
explains:
  E3: [ProbabilityTheory.moment, ProbabilityTheory.mgf, ProbabilityTheory.measure_ge_le_exp_mul_mgf, ProbabilityTheory.iIndepFun.mgf_sum, ProbabilityTheory.HasSubgaussianMGF, ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun]
  E2: [ProbabilityTheory.centralMoment, ProbabilityTheory.centralMoment_two_eq_variance, ProbabilityTheory.cgf, ProbabilityTheory.IndepFun.mgf_add, ProbabilityTheory.measure_ge_le_exp_cgf, ProbabilityTheory.mgf_pos, ProbabilityTheory.integrableExpSet, ProbabilityTheory.analyticOn_mgf, ProbabilityTheory.iteratedDeriv_mgf, ProbabilityTheory.iteratedDeriv_mgf_zero, ProbabilityTheory.deriv_mgf_zero, ProbabilityTheory.complexMGF, MeasureTheory.Measure.ext_of_complexMGF_eq, ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero, ProbabilityTheory.HasSubgaussianMGF.measure_ge_le]
  E1: auto
families: []
requires: [V03, V13, V15, V20.C01, V20.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Moments and generating functions

### Overview

The moments $E[X^n]$ of a variable give more information about its law than the mean and the variance. The moment generating function $M_X(t) = E[e^{tX}]$ collects all the moments into one function: where it is finite near $0$, it is analytic and its derivatives at $0$ are the moments. It also converts sums of independent variables into products. With Markov's inequality applied to $e^{tX}$, it gives the Chernoff bound, an exponential bound on the tail of a sum, much stronger than the bound of Chebyshev. This section defines the moments and the generating function, proves the Chernoff bound and Hoeffding's inequality, and applies them to coin tosses.

### Definitions

**Definition (Moments).** Let $X$ be a real variable and $n \in \mathbb{N}$. The *moment of order $n$* is $E[X^n]$, and the *central moment of order $n$* is $E[(X - E[X])^n]$, when they exist. The central moment of order $2$ is the variance.

::: mathlib
`ProbabilityTheory.moment` · `Mathlib.Probability.Moments.Basic`

`moment X p μ = μ[X ^ p]` for `p : ℕ`, and `centralMoment X p μ = μ[(X - fun _ ↦ μ[X]) ^ p]`. Both are Bochner integrals with the junk value `0`. `centralMoment_two_eq_variance` connects them to Section 2.

<?decl ProbabilityTheory.moment?>
:::

**Definition (Moment generating function).** The *moment generating function* of $X$ is $M_X(t) = E[e^{tX}]$ for $t \in \mathbb{R}$. It is a number in $(0, \infty]$, and the set $D_X = \{t : E[e^{tX}] < \infty\}$ is an interval that contains $0$, by the convexity of $t \mapsto e^{tx}$. The *cumulant generating function* is $K_X(t) = \log M_X(t)$.

::: mathlib
`ProbabilityTheory.mgf` · `Mathlib.Probability.Moments.Basic`

`mgf X μ t = μ[fun ω ↦ rexp (t * X ω)]`, a real number. Where `exp (t * X)` is not integrable it has the junk value `0`, so `mgf_pos` needs the integrability. `cgf X μ t = log (mgf X μ t)`. The interval $D_X$ is `integrableExpSet X μ` in `Mathlib.Probability.Moments.IntegrableExpMul`, which also proves that each moment is finite when $0$ is in the interior of this set.

<?decl ProbabilityTheory.mgf?>
:::

The *complex* generating function $E[e^{zX}]$ for $z \in \mathbb{C}$ with $\operatorname{Re} z \in D_X$ is `complexMGF X μ z`. On the imaginary axis it is the characteristic function of Chapter 4.

### Theorems and proofs

**Theorem (Moments from the generating function).** Let $0$ be in the interior of $D_X$. Then all the moments of $X$ are finite, $M_X$ is analytic on the interior of $D_X$, and
$$M_X^{(n)}(0) = E[X^n], \qquad M_X(t) = \sum_{n \ge 0} \frac{E[X^n]}{n!} t^n \text{ near } 0.$$

*Proof.* Take $\delta > 0$ with $\pm\delta \in D_X$. Then $e^{\delta |x|} \le e^{\delta x} + e^{-\delta x}$, so $E[e^{\delta|X|}] < \infty$, and $|x|^n \le n!\,\delta^{-n} e^{\delta|x|}$ gives $E|X|^n < \infty$. For $|t| < \delta$, the series $e^{tX} = \sum_n t^n X^n / n!$ has the dominating function $\sum_n |t|^n |X|^n / n! = e^{|t||X|} \le e^{\delta|X|}$, which is integrable. The dominated convergence theorem of Volume 18 exchanges the sum and the expectation, so $M_X$ is the sum of a power series near $0$, with coefficients $E[X^n]/n!$. The same argument at each interior point gives the analyticity. $\square$

::: mathlib
`ProbabilityTheory.iteratedDeriv_mgf_zero` · `Mathlib.Probability.Moments.MGFAnalytic`

For `0 ∈ interior (integrableExpSet X μ)`: `iteratedDeriv n (mgf X μ) 0 = μ[X ^ n]`. The case `n = 1` is `deriv_mgf_zero`. At an interior point `t`, `iteratedDeriv_mgf` gives `μ[X ^ n * exp (t * X)]`, and `analyticOn_mgf` gives the analyticity on the interior.

<?decl ProbabilityTheory.iteratedDeriv_mgf_zero?>
:::

**Theorem (Generating function of a sum).** Let $X_1, \ldots, X_n$ be independent. Then $M_{X_1 + \cdots + X_n}(t) = M_{X_1}(t) \cdots M_{X_n}(t)$ for all $t$, in $[0, \infty]$.

*Proof.* $e^{t(X_1 + \cdots + X_n)} = e^{tX_1} \cdots e^{tX_n}$. The variables $e^{tX_i}$ are nonnegative and independent, because they are functions of independent variables. The product theorem for nonnegative variables of Section 1 gives the result. $\square$

So the cumulant generating function of a sum of independent variables is the sum of the cumulant generating functions.

::: mathlib
`ProbabilityTheory.iIndepFun.mgf_sum` · `Mathlib.Probability.Moments.Basic`

For `iIndepFun X μ` with measurable `X i` and a finset `s`: `mgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, mgf (X i) μ t`. Because of the junk value, the statement is true even where some factor is infinite. The two variable form is `IndepFun.mgf_add`, and the sum of cumulants is `iIndepFun.cgf_sum`.

<?decl ProbabilityTheory.iIndepFun.mgf_sum?>
:::

**Theorem (The generating function determines the law).** If $M_X$ and $M_Y$ are finite and equal on an open interval that contains $0$, then $X$ and $Y$ have the same law.

*Proof sketch.* The complex function $z \mapsto E[e^{zX}]$ is analytic on the strip $\{\operatorname{Re} z \in D_X\}$, by the argument of the first theorem. Two analytic functions on a connected open set that agree on a real interval agree everywhere (the identity theorem of complex analysis). So $E[e^{isX}] = E[e^{isY}]$ for all real $s$: the characteristic functions are equal, and Chapter 4 shows that the characteristic function determines the law. $\square$

::: mathlib
`MeasureTheory.Measure.ext_of_complexMGF_eq` · `Mathlib.Probability.Moments.ComplexMGF`

For finite measures and a.e. measurable `X`, `Y`: `complexMGF X μ = complexMGF Y μ' → μ.map X = μ'.map Y`. The step from the real interval to the strip is `eqOn_complexMGF_of_mgf`.

<?decl MeasureTheory.Measure.ext_of_complexMGF_eq?>
:::

**Theorem (Chernoff bound).** For each real $a$ and each $t \ge 0$ with $M_X(t) < \infty$,
$$P(X \ge a) \le e^{-ta} M_X(t), \qquad \text{so} \qquad P(X \ge a) \le \exp\Big(-\sup_{t \ge 0}\big(ta - K_X(t)\big)\Big).$$

*Proof.* The function $x \mapsto e^{tx}$ is nondecreasing for $t \ge 0$, so $\{X \ge a\} \subseteq \{e^{tX} \ge e^{ta}\}$. Markov's inequality gives $P(e^{tX} \ge e^{ta}) \le E[e^{tX}]/e^{ta}$. The second form takes the infimum over $t$. $\square$

::: mathlib
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` · `Mathlib.Probability.Moments.Basic`

For a finite measure, `0 ≤ t` and integrable `exp (t * X)`: `μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε) * mgf X μ t`. The form with the cumulant is `measure_ge_le_exp_cgf`, and the lower tail is `measure_le_le_exp_mul_mgf`.

<?decl ProbabilityTheory.measure_ge_le_exp_mul_mgf?>
:::

**Definition (Sub-Gaussian variable).** A real variable $X$ is *sub-Gaussian with parameter $c \ge 0$* if $E[e^{tX}] \le e^{ct^2/2}$ for all real $t$. A Gaussian variable with mean $0$ and variance $c$ has equality.

**Theorem (Hoeffding).** 1. If $a \le X \le b$ a.s. and $E[X] = 0$, then $X$ is sub-Gaussian with parameter $(b - a)^2/4$. 2. If $X_1, \ldots, X_n$ are independent and $X_i$ is sub-Gaussian with parameter $c_i$, then for $\varepsilon \ge 0$
$$P(X_1 + \cdots + X_n \ge \varepsilon) \le \exp\Big(-\frac{\varepsilon^2}{2(c_1 + \cdots + c_n)}\Big).$$

*Proof.* 1. Let $K(t) = \log E[e^{tX}]$. Then $K(0) = 0$ and $K'(0) = E[X] = 0$. The second derivative $K''(t)$ is the variance of $X$ under the tilted law $e^{tX - K(t)}\,dP$, which is again a law on $[a, b]$. By the bound of Section 2, $K''(t) \le (b - a)^2/4$. Taylor's formula gives $K(t) \le t^2(b - a)^2/8$. 2. By the product theorem, $E[e^{t \sum X_i}] = \prod_i E[e^{tX_i}] \le e^{t^2 \sum_i c_i/2}$. The Chernoff bound gives $P(\sum X_i \ge \varepsilon) \le \exp(-t\varepsilon + t^2 C/2)$ with $C = \sum c_i$. Take $t = \varepsilon/C$. $\square$

::: mathlib
`ProbabilityTheory.HasSubgaussianMGF` · `Mathlib.Probability.Moments.SubGaussian`

`HasSubgaussianMGF X c μ` for `c : ℝ≥0` is a structure: `exp (t * X)` is integrable for all `t`, and `mgf X μ t ≤ exp (c * t ^ 2 / 2)`. Part 1 of Hoeffding is `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, with parameter `(‖b - a‖₊ / 2) ^ 2`. Its proof uses the tilted measures of `Mathlib.Probability.Moments.Tilted` (`variance_tilted_mul`), as in the text. The tail bound for one variable is `HasSubgaussianMGF.measure_ge_le`. The file also has a conditional form for martingale differences, the Azuma-Hoeffding inequality.

<?decl ProbabilityTheory.HasSubgaussianMGF?>
:::

::: mathlib
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` · `Mathlib.Probability.Moments.SubGaussian`

For `iIndepFun X μ`, `HasSubgaussianMGF (X i) (c i) μ` for `i ∈ s` and `0 ≤ ε`: `μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i))`. This is part 2 of Hoeffding.

<?decl ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun?>
:::

### Examples

**Example (A Chernoff bound for coin tosses).** Toss a fair coin $n$ times and let $S_n$ be the number of heads. Put $X_i = \mathbf{1}_{\{\text{heads at } i\}} - 1/2$, with values in $[-1/2, 1/2]$ and mean $0$. By part 1 of Hoeffding, $X_i$ is sub-Gaussian with parameter $1/4$. Part 2 with $\varepsilon = an$ gives
$$P(S_n \ge (1/2 + a)n) \le \exp\Big(-\frac{a^2 n^2}{2 \cdot n/4}\Big) = e^{-2a^2 n}.$$
For $n = 1000$ and $a = 0.1$, the probability of at least $600$ heads is at most $e^{-20} \approx 2.1 \times 10^{-9}$. Chebyshev with $\operatorname{Var}(S_n) = 250$ gives only $P(|S_n - 500| \ge 100) \le 250/10^4 = 0.025$.

**Example (Generating functions of the binomial law).** For $P(X = 1) = p$ and $P(X = 0) = 1 - p$, $M_X(t) = 1 - p + pe^t$. So the binomial variable $S_n$ of Section 2 has $M_{S_n}(t) = (1 - p + pe^t)^n$. Then $M_{S_n}'(0) = np$ and $M_{S_n}''(0) = n(n-1)p^2 + np$, so $E[S_n^2] - (E S_n)^2 = np(1 - p)$, as in Section 2.

**Counterexample (Moments do not determine the law).** Let $X$ be lognormal: $X = e^Z$ with $Z$ standard Gaussian. Then $E[X^n] = e^{n^2/2}$ for all $n$, but $E[e^{tX}] = \infty$ for each $t > 0$, so the theorem on the generating function does not apply. The variable $Y$ with density $f(x)(1 + \sin(2\pi \log x))$, where $f$ is the density of $X$, has the same moments as $X$ and a different law. This example is due to Heyde (1963).

### The library around it

`Mathlib.Probability.Moments.Basic` has the definitions and the elementary rules: `mgf_const_add`, `mgf_const_mul`, `mgf_neg`, the law form `mgf_map`, and the sums `iIndepFun.mgf_sum` and `mgf_sum_of_identDistrib` for i.i.d. variables. `Mathlib.Probability.Moments.IntegrableExpMul` proves the integrability of $|X|^p e^{tX}$ on the interior of `integrableExpSet`. `Mathlib.Probability.Moments.MGFAnalytic` has the derivatives and the analyticity, and `Mathlib.Probability.Moments.ComplexMGF` the complex extension and the uniqueness theorem. `Mathlib.Probability.Moments.SubGaussian` develops the sub-Gaussian bounds, for measures and for kernels, with conditional versions for martingales.

Common errors of a learner:

- `mgf X μ t` is a real number with the junk value `0`, not a value in `ℝ≥0∞`. A proof that uses `mgf X μ t > 0` needs the integrability of `exp (t * X)`.
- The analyticity of `mgf` holds on `interior (integrableExpSet X μ)`, which may be empty except for the point `0`; then no derivative at `0` exists.
- `HasSubgaussianMGF X c μ` has `c : ℝ≥0`, the variance parameter, not the standard deviation.

### Exercises

1. (A) Compute $M_X$ for $X$ uniform on $\{1, \ldots, 6\}$ and for $X$ uniform on $[0, 1]$.
2. (A) Show that $M_{aX + b}(t) = e^{bt} M_X(at)$.
3. (A) Let $X$ be Poisson with parameter $\lambda$ (Chapter 4). Show that $M_X(t) = \exp(\lambda(e^t - 1))$ and deduce $E[X] = \operatorname{Var}(X) = \lambda$.
4. (B) Show that $K_X''(0) = \operatorname{Var}(X)$ when $0$ is interior to $D_X$.
5. (B) Show that $D_X = \{0\}$ for the Cauchy law with density $1/(\pi(1 + x^2))$.
6. (B) Let $S_n$ be binomial with parameters $n, 1/2$. Use the Chernoff bound with the optimal $t$ to show $P(S_n \ge (1/2 + a) n) \le e^{-n I(a)}$, where $I(a) = (1/2 + a)\log(1 + 2a) + (1/2 - a)\log(1 - 2a)$, and compare $I(a)$ with $2a^2$.
7. (B) Let $X_1, \ldots, X_n$ be independent with $|X_i| \le 1$ and mean $0$. Show that $P(|X_1 + \cdots + X_n| \ge \varepsilon) \le 2e^{-\varepsilon^2/(2n)}$.
8. (C) Show that $D_X$ is an interval and that $\log M_X$ is convex on it, with Hölder's inequality.

### Notes and history

Laplace used generating functions systematically in his *Théorie analytique des probabilités* of 1812. Chernoff published his bound in 1952 in a paper on tests of hypotheses, and Hoeffding his inequality for bounded variables in 1963. The example of a law that its moments do not determine is due to Stieltjes for related densities, and the form with the lognormal law is due to Heyde (1963).

### Reference

<?reference?>
