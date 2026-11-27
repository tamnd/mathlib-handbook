---
title: Monotone convergence and Fatou's lemma
kind: theory
modules:
  - Mathlib.MeasureTheory.Integral.Lebesgue.Add
  - Mathlib.MeasureTheory.Integral.Lebesgue.Countable
  - Mathlib.MeasureTheory.Integral.Lebesgue.Markov
  - Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
  - Mathlib.MeasureTheory.Integral.Lebesgue.Map
  - Mathlib.MeasureTheory.Integral.Lebesgue.Sub
explains:
  E3: [MeasureTheory.lintegral_iSup, MeasureTheory.lintegral_add_left, MeasureTheory.lintegral_liminf_le, MeasureTheory.mul_meas_ge_le_lintegral, MeasureTheory.tendsto_lintegral_of_dominated_convergence]
  E2: [MeasureTheory.lintegral_eq_iSup_eapprox_lintegral, MeasureTheory.lintegral_add_right, MeasureTheory.lintegral_tsum, MeasureTheory.lintegral_const_mul, MeasureTheory.ae_lt_top, MeasureTheory.lintegral_sub, MeasureTheory.lintegral_iInf, MeasureTheory.lintegral_map, MeasureTheory.lintegral_dirac, MeasureTheory.lintegral_count]
  E1: auto
families: []
requires: [V04, V13, V18.C01, V18.C02, V18.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monotone convergence and Fatou's lemma

### Overview

The definition of Section 1 makes monotonicity free, but additivity is not visible: a simple function below $f + g$ need not split into one below $f$ and one below $g$. The way out is a limit theorem. The monotone convergence theorem says that the integral commutes with increasing limits. With the approximation theorem of Section 1 it gives additivity, series and the lemma of Fatou. The section ends with the inequality of Markov and the dominated convergence theorem for functions with values in $[0, \infty]$. All functions are measurable maps $X \to [0, \infty]$ unless the text says otherwise.

### Definitions

**Definition (Limit inferior of functions).** For functions $f_n : X \to [0, \infty]$, $\liminf_n f_n$ is the function $x \mapsto \sup_n \inf_{k \ge n} f_k(x)$. It is measurable when every $f_n$ is, by Chapter 1.

### Theorems and proofs

**Lemma (Finite simple functions suffice).** For every $f \ge 0$, $\int f \, d\mu$ is the supremum of $\int \varphi \, d\mu$ over the simple $\varphi \le f$ with finite values.

*Proof.* Let $\varphi \le f$ be simple and $\varphi_k = \min(\varphi, k)$. Each $\varphi_k$ is simple with finite values and $\varphi_k \le f$. Its integral is $\sum_y \min(y, k) \, \mu(\varphi^{-1}(\{y\}))$, a finite sum of terms that increase to $y \, \mu(\varphi^{-1}(\{y\}))$. So $\int \varphi_k \, d\mu \to \int \varphi \, d\mu$. $\square$

**Theorem (Monotone convergence).** Let $f_1 \le f_2 \le \dots$ be measurable and $f = \sup_n f_n$. Then $\int f \, d\mu = \sup_n \int f_n \, d\mu$.

*Proof.* Each $f_n \le f$, so $\sup_n \int f_n \, d\mu \le \int f \, d\mu$ by monotonicity. For the other inequality, let $\varphi \le f$ be simple with finite values, and let $0 < r < 1$. Put $E_n = \{x : r \varphi(x) \le f_n(x)\}$. The set $E_n$ is measurable, because $\varphi$ and $f_n$ are measurable, and $E_n \subseteq E_{n+1}$ because the $f_n$ increase. The union of the $E_n$ is $X$. If $\varphi(x) = 0$, then $x \in E_1$. If $\varphi(x) > 0$, then $r \varphi(x) < \varphi(x) \le f(x) = \sup_n f_n(x)$, since $\varphi(x)$ is finite, so $r \varphi(x) \le f_n(x)$ for some $n$.

The simple function $r \varphi \mathbf{1}_{E_n}$ is below $f_n$. The partition formula of Section 1 gives
$$\int f_n \, d\mu \ge \int r \varphi \mathbf{1}_{E_n} \, d\mu = r \sum_y y \, \mu(\varphi^{-1}(\{y\}) \cap E_n).$$
By continuity from below (Chapter 2), $\mu(\varphi^{-1}(\{y\}) \cap E_n) \to \mu(\varphi^{-1}(\{y\}))$ for each of the finitely many $y$. So $\sup_n \int f_n \, d\mu \ge r \int \varphi \, d\mu$. Let $r \to 1$, and take the supremum over $\varphi$ with the lemma. $\square$

::: mathlib
`MeasureTheory.lintegral_iSup` · `Mathlib.MeasureTheory.Integral.Lebesgue.Add`

`(∀ n, Measurable (f n)) → Monotone f → ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ`. The form `lintegral_iSup'` takes `AEMeasurable` functions and an almost everywhere monotone sequence. With `eapprox`, the theorem gives `lintegral_eq_iSup_eapprox_lintegral`: `∫⁻ f` is the supremum of the integrals of `eapprox f n`.

<?decl MeasureTheory.lintegral_iSup?>
<?decl MeasureTheory.lintegral_eq_iSup_eapprox_lintegral?>
:::

**Theorem (Additivity).** For measurable $f, g$ and $c \in [0, \infty]$, $\int (f + g) \, d\mu = \int f \, d\mu + \int g \, d\mu$ and $\int c f \, d\mu = c \int f \, d\mu$.

*Proof.* Take increasing simple $\varphi_n \to f$ and $\psi_n \to g$ by the approximation theorem of Section 1. Then $\varphi_n + \psi_n$ is simple and increases to $f + g$. Monotone convergence three times, and the additivity of the simple integral, give
$$\int (f + g) \, d\mu = \sup_n \Big( \int \varphi_n \, d\mu + \int \psi_n \, d\mu \Big) = \int f \, d\mu + \int g \, d\mu.$$
The supremum of a sum of two increasing sequences in $[0, \infty]$ is the sum of the suprema. For $cf$, the functions $c \varphi_n$ increase to $cf$, and multiplication by $c$ commutes with increasing suprema in $[0, \infty]$. $\square$

**Corollary (Series).** For measurable $f_k \ge 0$, $\int \sum_{k=1}^\infty f_k \, d\mu = \sum_{k=1}^\infty \int f_k \, d\mu$.

*Proof.* Additivity and induction give the formula for finite sums. The partial sums increase to the series, so monotone convergence gives the formula for the series. $\square$

::: mathlib
`MeasureTheory.lintegral_add_left` · `Mathlib.MeasureTheory.Integral.Lebesgue.Add`

`Measurable f → ∀ g, ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ`. Only one function needs to be measurable. Mathlib proves the case of two measurable functions first, then replaces `g` by a measurable function below it with the same integral. The mirror form is `lintegral_add_right`. Series are `lintegral_tsum`, over any countable index type with `AEMeasurable` terms. Constants are `lintegral_const_mul`, for measurable `f`.

<?decl MeasureTheory.lintegral_add_left?>
<?decl MeasureTheory.lintegral_add_right?>
<?decl MeasureTheory.lintegral_tsum?>
<?decl MeasureTheory.lintegral_const_mul?>
:::

**Theorem (Markov inequality).** For $\varepsilon \in [0, \infty]$, $\varepsilon \, \mu(\{f \ge \varepsilon\}) \le \int f \, d\mu$. If $\int f \, d\mu < \infty$, then $f < \infty$ almost everywhere.

*Proof.* The set $A = \{f \ge \varepsilon\}$ is measurable, and $\varepsilon \mathbf{1}_A \le f$ at every point. Section 1 gives $\int \varepsilon \mathbf{1}_A \, d\mu = \varepsilon \mu(A)$, and monotonicity gives the inequality. For the second claim, $\{f = \infty\} \subseteq \{f \ge n\}$, so $\mu(\{f = \infty\}) \le \frac{1}{n} \int f \, d\mu$ for every $n \ge 1$. The right side tends to $0$. $\square$

::: mathlib
`MeasureTheory.mul_meas_ge_le_lintegral` · `Mathlib.MeasureTheory.Integral.Lebesgue.Markov`

`Measurable f → ∀ ε, ε * μ {x | ε ≤ f x} ≤ ∫⁻ a, f a ∂μ`. The form `mul_meas_ge_le_lintegral₀` takes `AEMeasurable f μ`, and `meas_ge_le_lintegral_div` divides by `ε` with `ε ≠ 0` and `ε ≠ ∞`. The second claim is `ae_lt_top`.

<?decl MeasureTheory.mul_meas_ge_le_lintegral?>
<?decl MeasureTheory.ae_lt_top?>
:::

**Theorem (Fatou's lemma).** For measurable $f_n \ge 0$, $\int \liminf_n f_n \, d\mu \le \liminf_n \int f_n \, d\mu$.

*Proof.* Put $g_n = \inf_{k \ge n} f_k$. Each $g_n$ is measurable, the $g_n$ increase, and $\sup_n g_n = \liminf_n f_n$. For $k \ge n$, $g_n \le f_k$, so $\int g_n \, d\mu \le \inf_{k \ge n} \int f_k \, d\mu$. Monotone convergence gives
$$\int \liminf_n f_n \, d\mu = \sup_n \int g_n \, d\mu \le \sup_n \inf_{k \ge n} \int f_k \, d\mu = \liminf_n \int f_n \, d\mu. \qquad \square$$

::: mathlib
`MeasureTheory.lintegral_liminf_le` · `Mathlib.MeasureTheory.Integral.Lebesgue.Add`

`∫⁻ a, liminf (fun i ↦ f i a) u ∂μ ≤ liminf (fun i ↦ ∫⁻ a, f i a ∂μ) u` for measurable `f i`. The index runs along any countably generated filter `u`. The form `lintegral_liminf_le'` takes `AEMeasurable` functions.

<?decl MeasureTheory.lintegral_liminf_le?>
:::

**Lemma (Subtraction).** Let $h \le g$ almost everywhere, with $h$ measurable and $\int h \, d\mu < \infty$. Then $\int (g - h) \, d\mu = \int g \, d\mu - \int h \, d\mu$.

*Proof.* Almost everywhere $g = (g - h) + h$. Additivity, with only $h$ measurable, gives $\int g \, d\mu = \int (g - h) \, d\mu + \int h \, d\mu$. Subtract the finite number $\int h \, d\mu$. $\square$

**Theorem (Dominated convergence for nonnegative functions).** Let $f_n$ be measurable, $f_n \to f$ almost everywhere, and $f_n \le g$ almost everywhere for a measurable $g$ with $\int g \, d\mu < \infty$. Then $\int f_n \, d\mu \to \int f \, d\mu$.

*Proof.* Replace $f$ by $\liminf_n f_n$. It is measurable, equal to $f$ almost everywhere, and has the same integral by Section 1. Fatou gives $\int f \, d\mu \le \liminf_n \int f_n \, d\mu$. For the upper bound, the functions $g - f_n$ are measurable and nonnegative. By the Markov inequality $g < \infty$ almost everywhere, and at such a point $\liminf_n (g - f_n) = g - \limsup_n f_n = g - f$. Fatou and the subtraction lemma give
$$\int g \, d\mu - \int f \, d\mu = \int (g - f) \, d\mu \le \liminf_n \Big( \int g \, d\mu - \int f_n \, d\mu \Big) = \int g \, d\mu - \limsup_n \int f_n \, d\mu.$$
Here $f \le g$ almost everywhere, and all integrals are at most $\int g \, d\mu < \infty$. So the terms are real numbers, and cancelling $\int g \, d\mu$ gives $\limsup_n \int f_n \, d\mu \le \int f \, d\mu$. $\square$

::: mathlib
`MeasureTheory.tendsto_lintegral_of_dominated_convergence` · `Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence`

The arguments are `bound`, `∀ n, Measurable (F n)`, `∀ n, F n ≤ᵐ[μ] bound`, `∫⁻ a, bound a ∂μ ≠ ∞`, and the almost everywhere limit. The bound needs no measurability. The upper half alone is `limsup_lintegral_le`. Decreasing sequences are `lintegral_iInf`, which asks `∫⁻ a, f 0 a ∂μ ≠ ∞`. The subtraction lemma is `lintegral_sub`.

<?decl MeasureTheory.tendsto_lintegral_of_dominated_convergence?>
<?decl MeasureTheory.lintegral_sub?>
<?decl MeasureTheory.lintegral_iInf?>
:::

### Examples

**Example (A series of bumps).** On $\mathbb{R}$ with Lebesgue measure, let $f = \sum_{n \ge 0} 2^n \mathbf{1}_{[n, n + 4^{-n})}$. The corollary on series gives $\int f \, d\lambda = \sum_n 2^n 4^{-n} = \sum_n 2^{-n} = 2$. The function is unbounded, and its integral is finite.

**Example (Double series).** Let $\mu$ be the counting measure on $\mathbb{N}$. For a simple $f$ with finite support, $\int f \, d\mu = \sum_n f(n)$, and monotone convergence extends this to every $f \ge 0$. Apply the corollary on series to $f_m(n) = a_{nm} \ge 0$:
$$\sum_n \sum_m a_{nm} = \sum_m \sum_n a_{nm}.$$
The value $\infty$ is allowed.

**Counterexample (Mass escapes to infinity).** Let $f_n = \mathbf{1}_{[n, n+1]}$ on $\mathbb{R}$. Then $f_n \to 0$ at every point, and $\int f_n \, d\lambda = 1$. Fatou's inequality is strict: $0 < 1$. The sequence is not increasing, so monotone convergence does not apply. The only bound is $\sup_n f_n = \mathbf{1}_{[0, \infty)}$, with infinite integral, so dominated convergence does not apply.

**Counterexample (Decreasing limits).** The functions $f_n = \mathbf{1}_{[n, \infty)}$ decrease to $0$, but every $\int f_n \, d\lambda$ is $\infty$. The finiteness hypothesis of `lintegral_iInf` is needed.

### The library around it

The theorems of this section are in the files `Lebesgue.Add`, `Lebesgue.Markov`, `Lebesgue.Sub` and `Lebesgue.DominatedConvergence` under `Mathlib.MeasureTheory.Integral`.

::: mathlib
`MeasureTheory.lintegral_map` · `Mathlib.MeasureTheory.Integral.Lebesgue.Map`

`∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ` for measurable `f` and `g`, with the pushforward `Measure.map` of Chapter 2.

<?decl MeasureTheory.lintegral_map?>
:::

::: mathlib
`MeasureTheory.lintegral_count` · `Mathlib.MeasureTheory.Integral.Lebesgue.Countable`

`∫⁻ a, f a ∂count = ∑' a, f a`, and `lintegral_dirac` gives `∫⁻ a, f a ∂(dirac a) = f a`. Both need `MeasurableSingletonClass`.

<?decl MeasureTheory.lintegral_count?>
<?decl MeasureTheory.lintegral_dirac?>
:::

Common errors of a learner:

- Applying monotone convergence to a sequence that converges but does not increase.
- Applying the theorem for decreasing sequences without a finite integral.
- Cancelling $\int g \, d\mu$ on both sides when it may be $\infty$.
- Forgetting the measurability of each $f_n$ in Fatou. The limit inferior needs no separate hypothesis.

### Exercises

1. (A) Compute $\int \sum_{n \ge 1} \mathbf{1}_{[0, 1/n]} \, d\lambda$.
2. (A) Show that $\mu(\{f \ge \varepsilon\}) = 0$ for every $\varepsilon > 0$ if $\int f \, d\mu = 0$, with the Markov inequality.
3. (A) Give a sequence $f_n$ on $[0, 1]$ with $\int f_n \, d\lambda \to 0$ and $f_n \to 0$ at no point. Hint: the typewriter sequence of indicators of dyadic intervals.
4. (B) Let $\int f \, d\mu < \infty$. Show that $\int_{\{f > n\}} f \, d\mu \to 0$. Hint: dominated convergence for $f \mathbf{1}_{\{f > n\}}$.
5. (B) Show that $A \mapsto \int_A f \, d\mu$ is a measure. Hint: the corollary on series for $f \mathbf{1}_{A_k}$.
6. (B) Let $A_k$ be measurable with $\sum_k \mu(A_k) < \infty$. Show that almost every $x$ lies in only finitely many $A_k$. Hint: integrate $\sum_k \mathbf{1}_{A_k}$ and use the Markov inequality.
7. (C) Let $\int f \, d\mu < \infty$. Show that for every $\varepsilon > 0$ there is $\delta > 0$ with $\int_A f \, d\mu < \varepsilon$ whenever $\mu(A) < \delta$. Hint: split $f = \min(f, n) + (f - \min(f, n))$ and use Exercise 4.

### Notes and history

The monotone convergence theorem is often called the theorem of Beppo Levi. Fatou proved his lemma in 1906. In Mathlib, the files of this section have Mario Carneiro and Johannes Hölzl as authors. Exercise 6 is the first lemma of Borel and Cantelli.

### Reference

<?reference?>
