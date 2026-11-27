---
title: Expectation
kind: theory
modules:
  - Mathlib.Probability.Independence.Integration
  - Mathlib.Probability.Independence.Integrable
explains:
  E3: [ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral, ProbabilityTheory.iIndepFun.integral_prod_eq_prod_integral, ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun]
  E2: [ProbabilityTheory.IndepFun.integrable_mul, ProbabilityTheory.IndepFun.integral_comp_mul_comp, ProbabilityTheory.indepFun_iff_integral_comp_mul, ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace, ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun, ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral, ProbabilityTheory.IndepFun.integrable_left_of_integrable_op, ProbabilityTheory.Indep.setIntegral_eq_mul]
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

## Expectation

### Overview

The expectation of a random variable is its integral with respect to the probability measure. Volume 18, Measure and integration, constructs the integral and proves its theorems: linearity, monotonicity, the monotone and dominated convergence theorems. This section does not prove them again. It shows how a probabilist uses them: the expectation as an average, the formula through the law, the formula through the tail, the inequalities of Markov and Jensen, and the one theorem that independence adds, that the expectation of a product of independent variables is the product of the expectations.

### Definitions

**Definition (Expectation).** Let $X$ be a real random variable on a probability space $(\Omega, \mathcal{F}, P)$. If $X \ge 0$, its *expectation* is $E[X] = \int_\Omega X\, dP \in [0, \infty]$. In general, $X$ is *integrable* if $E|X| < \infty$, and then $E[X] = E[X^+] - E[X^-]$, where $X^+ = \max(X, 0)$ and $X^- = \max(-X, 0)$. The expectation is also the *mean* of $X$.

For an event $A$, $E[\mathbf{1}_A] = P(A)$. For a variable with finitely many values, $E[X] = \sum_x x P(X = x)$, the average of the values, weighted by their probabilities.

::: mathlib
`MeasureTheory.integral` · `Mathlib.MeasureTheory.Integral.Bochner.Basic`

Mathlib has no separate definition of the expectation. The expectation is the Bochner integral `∫ ω, X ω ∂μ`, and `Mathlib.Probability.Notation` gives the notation `𝔼[X]` for `∫ ω, X ω` with respect to the measure `volume` of a `MeasureSpace`. The Bochner integral of a function that is not integrable has the junk value `0`. For a nonnegative variable with possibly infinite expectation, use the lower Lebesgue integral `∫⁻ ω, X ω ∂μ` with values in `ℝ≥0∞`.

<?decl MeasureTheory.integral?>
:::

### Theorems and proofs

The following properties are theorems of Volume 18 for each measure. For integrable $X$, $Y$ and real $a, b$:

1. *Linearity:* $E[aX + bY] = aE[X] + bE[Y]$.
2. *Monotonicity:* if $X \le Y$ a.s., then $E[X] \le E[Y]$.
3. *Constants:* $E[c] = c$, because $P(\Omega) = 1$.
4. *Transfer:* if $X$ has the law $\mu$ and $g$ is measurable with $g(X)$ integrable, $E[g(X)] = \int g\, d\mu$. Chapter 1 states this as `HasLaw.integral_comp`.

The fourth property says that the expectation of $g(X)$ depends only on the law of $X$. Two identically distributed variables have the same expectation.

**Theorem (Tail formula).** Let $X \ge 0$. Then
$$E[X] = \int_0^\infty P(X > t)\, dt.$$
If $X$ takes values in $\mathbb{N}$, then $E[X] = \sum_{n \ge 1} P(X \ge n)$.

*Proof.* For $x \ge 0$, $x = \int_0^\infty \mathbf{1}_{\{t < x\}}\, dt$. Apply this to $x = X(\omega)$ and integrate with respect to $P$. The integrand $(\omega, t) \mapsto \mathbf{1}_{\{t < X(\omega)\}}$ is nonnegative and measurable, so Tonelli's theorem of Volume 18 exchanges the integrals:
$$E[X] = \int_\Omega \int_0^\infty \mathbf{1}_{\{t < X(\omega)\}}\, dt\, dP(\omega) = \int_0^\infty P(X > t)\, dt.$$
For integer values, $P(X > t) = P(X \ge n)$ for $t \in [n - 1, n)$. $\square$

::: mathlib
`MeasureTheory.lintegral_eq_lintegral_meas_lt` · `Mathlib.MeasureTheory.Integral.Layercake`

For `f ≥ 0` a.e. and a.e. measurable: `∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ t in Ioi 0, μ {a | t < f a}`. The file proves the general layer cake formula $\int \varphi(f)\, d\mu = \int_0^\infty \varphi'(t)\mu(f > t)\, dt$, which gives the moments $E[X^p]$ from the tails.

<?decl MeasureTheory.lintegral_eq_lintegral_meas_lt?>
:::

**Theorem (Markov's inequality).** Let $X \ge 0$ and $a > 0$. Then $P(X \ge a) \le E[X]/a$.

*Proof.* $a \mathbf{1}_{\{X \ge a\}} \le X$ pointwise. Take expectations. $\square$

::: mathlib
`MeasureTheory.mul_meas_ge_le_integral_of_nonneg` · `Mathlib.MeasureTheory.Integral.Bochner.Basic`

For `0 ≤ᵐ[μ] f` and integrable `f`: `ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ`. The form with the lower integral and no integrability is `mul_meas_ge_le_lintegral`, and the form with a division is `meas_ge_le_lintegral_div`.

<?decl MeasureTheory.mul_meas_ge_le_integral_of_nonneg?>
:::

**Theorem (Jensen's inequality).** Let $\varphi : \mathbb{R} \to \mathbb{R}$ be convex and let $X$ and $\varphi(X)$ be integrable. Then $\varphi(E[X]) \le E[\varphi(X)]$.

*Proof.* A convex function lies above each of its supporting lines. Take the line at $m = E[X]$: there is a real $c$ with $\varphi(x) \ge \varphi(m) + c(x - m)$ for all $x$. Put $x = X$ and take expectations: $E[\varphi(X)] \ge \varphi(m) + c(E[X] - m) = \varphi(m)$. $\square$

Examples: $|E[X]| \le E|X|$, $(E[X])^2 \le E[X^2]$, and $e^{E[X]} \le E[e^X]$. The proof uses $P(\Omega) = 1$ in the step $E[\varphi(m)] = \varphi(m)$, and the inequality is false for a general measure.

::: mathlib
`ConvexOn.map_integral_le` · `Mathlib.Analysis.Convex.Integral`

For a probability measure, `g` convex and continuous on a closed convex set `s` that contains the values of `f`, with `f` and `g ∘ f` integrable: `g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ`. The variable may take values in a Banach space.

<?decl ConvexOn.map_integral_le?>
:::

**Theorem (Product of independent variables).** Let $X, Y$ be independent and integrable. Then $XY$ is integrable and $E[XY] = E[X]E[Y]$. For independent integrable $X_1, \ldots, X_n$, $E[X_1 \cdots X_n] = E[X_1] \cdots E[X_n]$.

*Proof.* Step 1, indicators: for $X = \mathbf{1}_A$ and $Y = \mathbf{1}_B$ with $A \in \sigma(X)$ and $B \in \sigma(Y)$, $E[\mathbf{1}_A \mathbf{1}_B] = P(A \cap B) = P(A)P(B)$. Step 2: by bilinearity the formula holds for nonnegative simple functions that are $\sigma(X)$ and $\sigma(Y)$ measurable. Step 3: for $X, Y \ge 0$, take increasing sequences of such simple functions $X_n \uparrow X$ and $Y_n \uparrow Y$. Then $X_n Y_n \uparrow XY$, and the monotone convergence theorem gives $E[XY] = E[X]E[Y]$ in $[0, \infty]$. Step 4: apply step 3 to $|X|$ and $|Y|$, which are independent by Section 2 of Chapter 2. So $E|XY| = E|X|E|Y| < \infty$. Then write $X = X^+ - X^-$ and $Y = Y^+ - Y^-$, expand, and apply step 3 to each of the four products. The formula for $n$ variables follows by induction, because $X_1 \cdots X_{n-1}$ is independent of $X_n$. $\square$

Step 3 gives a theorem of its own: for independent $X, Y \ge 0$, $E[XY] = E[X]E[Y]$ with no integrability assumption, in $[0, \infty]$.

::: mathlib
`ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral` · `Mathlib.Probability.Independence.Integration`

For `X Y : Ω → 𝕜` with `𝕜` the real or the complex numbers, `IndepFun X Y μ` and a.e. strong measurability: `∫ ω, (X * Y) ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ`. There is no integrability hypothesis. If one of the two variables is not integrable, both sides are `0`: the right side through the junk value, the left side because the product is then a.s. zero or not integrable (`IndepFun.integrable_left_of_integrable_op`). The integrability of the product is `IndepFun.integrable_mul`, and the version with functions of the variables is `IndepFun.integral_comp_mul_comp`.

<?decl ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral?>
:::

::: mathlib
`ProbabilityTheory.iIndepFun.integral_prod_eq_prod_integral` · `Mathlib.Probability.Independence.Integration`

For a finite family: `∫ ω, (∏ i, X i) ω ∂μ = ∏ i, ∫ ω, X i ω ∂μ`. The form for nonnegative variables with the lower integral, step 3 of the proof, is `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun` for two variables and `lintegral_prod_eq_prod_lintegral_of_indepFun` for a finset.

<?decl ProbabilityTheory.iIndepFun.integral_prod_eq_prod_integral?>
:::

::: mathlib
`ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun` · `Mathlib.Probability.Independence.Integration`

For measurable `f g : Ω → ℝ≥0∞` and `IndepFun f g μ`: `∫⁻ ω, (f * g) ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ`. The version for two independent σ-algebras is `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace`.

<?decl ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun?>
:::

The converse also holds when the test functions are free: `indepFun_iff_integral_comp_mul` says that $X$ and $Y$ are independent if and only if $E[\varphi(X)\psi(Y)] = E[\varphi(X)]E[\psi(Y)]$ for all measurable $\varphi, \psi$ with integrable compositions. With indicators, this is the definition.

### Examples

**Example (Fixed points of a random permutation).** Let $\sigma$ be uniform on the $n!$ permutations of $\{1, \ldots, n\}$, and let $F$ be the number of fixed points. Write $F = \sum_{i=1}^n \mathbf{1}_{A_i}$ with $A_i = \{\sigma(i) = i\}$. Then $P(A_i) = (n - 1)!/n! = 1/n$, so linearity gives $E[F] = n \cdot (1/n) = 1$. The events $A_i$ are not independent, but linearity does not need independence. A direct computation of the law of $F$ is much harder.

**Example (The coupon collector).** Each box of cereal holds one of $n$ coupons, uniform and independent from box to box. Let $T$ be the number of boxes bought until all $n$ coupons are present. After $k$ distinct coupons, the number of boxes until a new coupon is geometric with success probability $(n - k)/n$, with mean $n/(n - k)$ (Chapter 4). So
$$E[T] = \sum_{k=0}^{n-1} \frac{n}{n - k} = n\Big(1 + \frac12 + \cdots + \frac1n\Big) = n H_n \approx n \log n.$$
For $n = 50$ this is about $225$ boxes.

**Counterexample (The St. Petersburg game).** A fair coin is tossed until it shows heads. If this happens at toss $k$, the player gets $2^k$. Let $X$ be the gain. Then $P(X = 2^k) = 2^{-k}$, and $E[X] = \sum_k 2^k 2^{-k} = \infty$. So $X$ is not integrable, and the Bochner integral of Mathlib gives the junk value $0$, while the lower integral gives $\infty$. A fair price for the game does not exist in the sense of the expectation.

**Example (The tail formula for a geometric variable).** Let $P(N \ge n) = q^{n-1}$ for $n \ge 1$, with $0 < q < 1$. The tail formula gives $E[N] = \sum_{n \ge 1} q^{n-1} = 1/(1 - q)$ in one line.

### The library around it

The file `Mathlib.Probability.Independence.Integration` has the product formulas, for two variables and for families, for real, complex and $\mathbb{R}_{\ge 0}^\infty$ values, and for smul and bilinear maps (`IndepFun.integral_bilin`, `IndepFun.integral_smul_eq_smul_integral`). The file `Mathlib.Probability.Independence.Integrable` goes in the other direction: `IndepFun.integrable_left_of_integrable_op` says that if $X$ and $Y$ are independent, $Y$ is not a.s. zero and $X \cdot Y$ is integrable, then $X$ is integrable. The lemma `Indep.setIntegral_eq_mul` computes $E[f(X); A]$ for $A$ in a σ-algebra independent of $X$.

All the general theorems of integration are in `MeasureTheory`, and Volume 18 is the place to read them. The main ones for probability are `integral_add`, `integral_mono`, `integral_map` (transfer), `tendsto_integral_of_dominated_convergence` and `lintegral_iSup` (monotone convergence).

Common errors of a learner:

- `∫ ω, X ω ∂μ = 0` does not imply that the mean is zero: `X` may be non-integrable. A proof about expectations often needs `Integrable X μ` from the start.
- The integrability of a variable on a probability space is not automatic for bounded variables in Lean: it follows from `Integrable.of_bound` or from `integrable_const` and `Integrable.mono`, with a measurability proof.
- `ENNReal.ofReal` and `ENNReal.toReal` are necessary to move between `∫⁻` and `∫`; `integral_eq_lintegral_of_nonneg_ae` is the bridge.

### Exercises

1. (A) Let $X$ be the result of a fair die. Compute $E[X]$ and $E[X^2]$.
2. (A) Let $X \ge 0$ with $E[X] = 0$. Show that $X = 0$ a.s.
3. (A) Let $X$ be integrable. Show that $P(|X| \ge a) \le E|X|/a$ for $a > 0$, and that $P(|X| = \infty) = 0$.
4. (B) In $n$ tosses of a fair coin, let $R$ be the number of runs (maximal blocks of equal results). Show that $E[R] = 1 + (n - 1)/2$.
5. (B) Let $X \ge 0$ be a variable with $E[X^2] < \infty$. Show that $P(X > 0) \ge (E[X])^2/E[X^2]$ (the second moment method). Use the Cauchy-Schwarz inequality for $X = X \mathbf{1}_{\{X > 0\}}$.
6. (B) Show that $E[1/X] \ge 1/E[X]$ for $X > 0$ with both sides finite.
7. (B) Let $X, Y$ be independent and uniform on $[0, 1]$. Compute $E[XY]$, $E[\max(X, Y)]$ and $E[|X - Y|]$.
8. (C) Let $X_1, \ldots, X_n$ be independent with $E[X_i] = 0$ and $E[X_i^4] \le K$. Show that $E[(X_1 + \cdots + X_n)^4] \le 3n^2 K$, by expansion and independence. Chapter 5 uses this bound.

### Notes and history

Huygens computed expectations of games in his treatise of 1657, *De ratiociniis in ludo aleae*, and took the expectation, not the probability, as the basic notion. The St. Petersburg game is due to Nicolaus Bernoulli in 1713; Daniel Bernoulli published his analysis of it in 1738 in the journal of the academy of St. Petersburg, which gave the game its name. Kolmogorov's book of 1933 defined the expectation as the Lebesgue integral.

### Reference

<?reference?>
