---
title: Harmonic numbers and the Euler-Mascheroni constant
kind: api
modules:
  - Mathlib.NumberTheory.Harmonic.Defs
  - Mathlib.NumberTheory.Harmonic.Bounds
  - Mathlib.NumberTheory.Harmonic.Int
  - Mathlib.NumberTheory.Harmonic.EulerMascheroni
  - Mathlib.NumberTheory.Harmonic.GammaDeriv
  - Mathlib.NumberTheory.Harmonic.ZetaAsymp
explains:
  E2: [harmonic, harmonic_le_one_add_log, harmonic_not_int, padicValRat_two_harmonic, Real.eulerMascheroniConstant, Real.tendsto_harmonic_sub_log, Real.eulerMascheroniConstant_eq_neg_deriv, tendsto_riemannZeta_sub_one_div, riemannZeta_one, riemannZeta_eq_inv_sub_add]
  E1: auto
families: []
requires: [V15, V19]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Harmonic numbers and the Euler-Mascheroni constant

### Overview

The $n$-th harmonic number is $H_n = 1 + \frac12 + \cdots + \frac1n$. It grows like $\log n$, and the difference $H_n - \log n$ tends to a constant $\gamma = 0.5772\ldots$, the Euler-Mascheroni constant. The constant appears in the derivative of the Gamma function at $1$, $\Gamma'(1) = -\gamma$, and in the Laurent expansion of the Riemann zeta function at its pole,
$$\zeta(s) = \frac{1}{s - 1} + \gamma + O(s - 1).$$
On the arithmetic side, $H_n$ is never an integer for $n \geq 2$, because its $2$-adic valuation is negative.

The modules `Mathlib.NumberTheory.Harmonic.Defs`, `Mathlib.NumberTheory.Harmonic.Bounds` and `Mathlib.NumberTheory.Harmonic.Int` define $H_n$ as a rational number, bound it by logarithms and prove the non-integrality. The module `Mathlib.NumberTheory.Harmonic.EulerMascheroni` defines $\gamma$ as a limit and bounds it. The module `Mathlib.NumberTheory.Harmonic.GammaDeriv` computes the derivative of $\Gamma$ at the positive integers and at $\frac12$, and the module `Mathlib.NumberTheory.Harmonic.ZetaAsymp` proves the expansion of $\zeta$ at $s = 1$. The last module depends on the zeta function of Section 4.

### The library around it

#### Harmonic numbers

`harmonic n` is the rational number $\sum_{i < n}\frac{1}{i + 1}$, so `harmonic 0` is $0$ by `harmonic_zero`, and `harmonic_succ` gives $H_{n+1} = H_n + \frac{1}{n + 1}$. The form $\sum_{i=1}^{n}\frac1i$ is `harmonic_eq_sum_Icc`. Since the value is in `ℚ`, statements about logarithms cast it to `ℝ`.

**Theorem.** For each $n$, $\log(n + 1) \leq H_n$, and for $n \geq 1$, $H_n \leq 1 + \log n$.

*Proof.* The function $1/x$ is decreasing. So $\frac1i \geq \int_i^{i+1}\frac{dx}{x}$, and the sum over $1 \leq i \leq n$ gives $H_n \geq \log(n + 1)$. In the same way $\frac1i \leq \int_{i-1}^{i}\frac{dx}{x}$ for $i \geq 2$, and the sum over $2 \leq i \leq n$ gives $H_n - 1 \leq \log n$. $\square$

These are `log_add_one_le_harmonic` and `harmonic_le_one_add_log`. The versions for a real argument, with $H_{\lfloor x \rfloor}$, are `log_le_harmonic_floor` and `harmonic_floor_le_one_add_log`. Both bounds together show $H_n \to \infty$ like $\log n$, so the harmonic series diverges.

#### Non-integrality

**Theorem.** For $n \geq 2$, $H_n$ is not an integer. More exactly, $v_2(H_n) = -\lfloor\log_2 n\rfloor$.

*Proof.* Let $2^k$ be the largest power of $2$ with $2^k \leq n$. Among $1, \ldots, n$ only $2^k$ has $v_2 = k$, and all other terms $\frac1i$ have $v_2(\frac1i) > -k$. By the strict triangle inequality for valuations, $v_2(H_n) = -k$. For $n \geq 2$, $k \geq 1$, so $H_n$ has an even denominator. $\square$

The valuation statement is `padicValRat_two_harmonic`, with `Nat.log 2 n` for $\lfloor\log_2 n\rfloor$, and `padicNorm_two_harmonic` is the version with the $2$-adic norm. The non-integrality is `harmonic_not_int`, stated as a statement that the rational number is not an integer. The positivity $H_n > 0$ for $n \neq 0$ is `harmonic_pos`. The $p$-adic valuation is the one of Chapter 1.

#### The Euler-Mascheroni constant

The library uses two sequences:

| Lean name | Value | Monotonicity |
|---|---|---|
| `Real.eulerMascheroniSeq n` | $H_n - \log(n + 1)$ | strictly increasing, `Real.strictMono_eulerMascheroniSeq` |
| `Real.eulerMascheroniSeq' n` | $H_n - \log n$, and $2$ at $n = 0$ | strictly decreasing, `Real.strictAnti_eulerMascheroniSeq'` |

Each term of the first sequence is below each term of the second, by `Real.eulerMascheroniSeq_lt_eulerMascheroniSeq'`. So both sequences converge, and the difference $\log(n + 1) - \log n$ tends to $0$, so they have the same limit. The constant `Real.eulerMascheroniConstant`, with the notation $\gamma$, is the limit of the first sequence. The limits are `Real.tendsto_eulerMascheroniSeq` and `Real.tendsto_eulerMascheroniSeq'`, and in the usual form:

**Theorem.** $H_n - \log n \to \gamma$ and $H_n - \log(n + 1) \to \gamma$ as $n \to \infty$.

These are `Real.tendsto_harmonic_sub_log` and `Real.tendsto_harmonic_sub_log_add_one`. The constant lies strictly between the terms of the two sequences, by `Real.eulerMascheroniSeq_lt_eulerMascheroniConstant` and `Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'`. A computation of the terms at $n = 6$ gives the bounds $\frac12 < \gamma < \frac23$, which are `Real.one_half_lt_eulerMascheroniConstant` and `Real.eulerMascheroniConstant_lt_two_thirds`, from `Real.one_half_lt_eulerMascheroniSeq_six` and `Real.eulerMascheroniSeq'_six_lt_two_thirds`.

#### The derivative of the Gamma function

The module `Mathlib.NumberTheory.Harmonic.GammaDeriv` connects $\gamma$ with the Gamma function of Volume 15.

| Lean name | Statement |
|---|---|
| `Real.hasDerivAt_Gamma_one` | $\Gamma'(1) = -\gamma$ |
| `Real.eulerMascheroniConstant_eq_neg_deriv` | $\gamma = -\Gamma'(1)$ |
| `Real.hasDerivAt_Gamma_nat` | $\Gamma'(n + 1) = n!\,(H_n - \gamma)$ |
| `Real.hasDerivAt_Gamma_one_half` | $\Gamma'(\frac12) = -\sqrt\pi\,(\gamma + 2\log 2)$ |
| `Real.eulerMascheroniConstant_eq_neg_integral_log` | $\gamma = -\int_0^\infty \log(t)\,e^{-t}\,dt$ |

The proof of the third line studies $f = \log\Gamma$. The relation $\Gamma(x + 1) = x\Gamma(x)$ gives $f'(n + 1) = f'(n) + \frac1n$, so $f'(n + 1) = f'(1) + H_n$. The convexity of $f$, from the Bohr-Mollerup theorem, shows $f'(n) = \log n + o(1)$. Together with $H_n - \log n \to \gamma$ this gives $f'(1) = -\gamma$, and then $\Gamma'(n + 1) = \Gamma(n + 1)f'(n + 1) = n!\,(H_n - \gamma)$. The value at $\frac12$ follows from the duplication formula. The complex versions are `Complex.hasDerivAt_Gamma_one`, `Complex.hasDerivAt_Gamma_nat` and `Complex.hasDerivAt_Gamma_one_half`. The fifth line is the derivative of $\Gamma(s) = \int_0^\infty t^{s-1}e^{-t}\,dt$ at $s = 1$, and `Real.eulerMascheroniConstant_eq_neg_integral_log_log` is a related integral formula.

#### The zeta function at s = 1

The module `Mathlib.NumberTheory.Harmonic.ZetaAsymp` proves the Laurent expansion of $\zeta$ at $s = 1$.

**Theorem.** $\zeta(s) - \frac{1}{s - 1} \to \gamma$ as $s \to 1$, $s \neq 1$.

This is `tendsto_riemannZeta_sub_one_div`. The proof first works on the real axis. For real $s \geq 1$ let $F(s) = \sum_{n \geq 1}\int_n^{n+1}\frac{x - n}{x^{s+1}}\,dx$. Then $F$ is continuous on $[1, \infty)$, $F(1) = 1 - \gamma$, and $F(s) = \frac{1}{s - 1} - \frac{\zeta(s)}{s}$ for $s > 1$. These three facts give the limit from the right, and the auxiliary functions are in the namespace ZetaAsymptotics. The complex statement follows from the theorem on removable singularities, since $\zeta(s) - \frac{1}{s - 1}$ is differentiable on a punctured neighbourhood of $1$ and bounded near $1$.

The library packages the expansion in two functions. `riemannZeta₀ s` is $\zeta(s) - \frac{1}{s - 1}$ for $s \neq 1$ and $\gamma$ at $s = 1$. It is entire, `differentiable_riemannZeta₀`, and `riemannZeta_eq_inv_sub_add` says $\zeta(s) = \frac{1}{s - 1} + \zeta_0(s)$ for $s \neq 1$. The function `riemannZeta₁ s` is $1 + (s - 1)\zeta_0(s)$, the entire extension of $(s - 1)\zeta(s)$. Consequences:

1. `riemannZeta_one`: the junk value $\zeta(1)$ of the definition is $\frac12(\gamma - \log 4\pi)$, and `riemannZeta_one_ne_zero` says it is not $0$.
2. `deriv_riemannZeta_zero`: $\zeta'(0) = -\frac12\log 2\pi$.
3. `log_deriv_riemannZeta_add_inv_sub_bounded`: $\frac{\zeta'(s)}{\zeta(s)} + \frac{1}{s - 1}$ is bounded near $s = 1$.
4. `riemannZeta_eventually_ne_zero_nhds_one`: $\zeta$ has no zeros near $s = 1$.
5. `riemannZeta_conj`: $\zeta(\bar s) = \overline{\zeta(s)}$.

The bound on the logarithmic derivative is the form in which the pole of $\zeta$ enters the proofs on the distribution of primes in Chapter 7.

#### Common errors

1. `harmonic n` sums $n$ terms, $\frac11$ to $\frac1n$, and it is a rational number. A real statement needs the cast, such as `(harmonic n : ℝ)`.
2. `Real.eulerMascheroniSeq n` is $H_n - \log(n + 1)$, not $H_n - \log n$. The second sequence is `Real.eulerMascheroniSeq'`, and its value at $0$ is the arbitrary value $2$.
3. `riemannZeta 1` is a number, $\frac12(\gamma - \log 4\pi)$, not the pole. The pole is visible only in limits such as `tendsto_riemannZeta_sub_one_div`, or in the function `riemannZeta₀`.

### Exercises

1. (A) Compute $H_1$ to $H_6$, and check `padicValRat_two_harmonic` for each of them.
2. (A) Use `log_add_one_le_harmonic` to show that the series $\sum_n \frac1n$ diverges.
3. (B) Show that $\Gamma'(2) = 1 - \gamma$ and $\Gamma'(3) = 3 - 2\gamma$ from `Real.hasDerivAt_Gamma_nat`.
4. (B) Show that $H_n - \log(n + 1)$ is strictly increasing, from $\frac{1}{n + 1} > \log(n + 2) - \log(n + 1)$.
5. (B) Let $p$ be an odd prime and $p \leq n < 2p$. Show that $v_p(H_n) = -1$, by the argument of `padicValRat_two_harmonic`.
6. (C) Use `riemannZeta_eq_inv_sub_add` and `riemannZeta_one` to compute $\zeta_0(1) - \zeta(1)$.

### Reference

<?reference?>
