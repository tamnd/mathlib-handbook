---
title: Stirling's formula
kind: theory
modules:
  - Mathlib.Analysis.Real.Pi.Wallis
explains:
  E3: [Real.Wallis.W]
  E2: [Real.Wallis.W_eq_factorial_ratio, Real.Wallis.W_pos, Real.Wallis.W_le, Real.Wallis.le_W, Real.Wallis.tendsto_W_nhds_pi_div_two, Real.Wallis.W_eq_integral_sin_pow_div_integral_sin_pow, Real.tendsto_prod_pi_div_two]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C02, V15.C03, V15.C05, V15.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Stirling's formula

### Overview

The factorial $n! = 1 \cdot 2 \cdots n$ grows fast, and its exact value is hard to compute for large $n$. Stirling's formula gives its size:
$$n! \sim \sqrt{2\pi n}\left(\frac{n}{e}\right)^n \qquad (n \to \infty).$$
For $n = 10$ the right side is $3598695.6$, and $10! = 3628800$, so the ratio is $1.0084$. The relative error tends to $0$, and it is close to $\frac{1}{12n}$.

The formula is a statement $u \sim v$ in the sense of Section 1, and its proof uses most of the tools of this volume. The proof has two parts. The first part shows that the sequence
$$s_n = \frac{n!}{\sqrt{2n}\,(n/e)^n}$$
decreases and has a positive limit $a$, with the series of the logarithm. The second part shows that $a = \sqrt{\pi}$, with Wallis's product, a formula for $\pi/2$ that comes from the integrals $\int_0^\pi \sin^n x\,dx$. This is the proof in Mathlib, and this section follows it step by step.

### Definitions

The integrals of this section are the Riemann integrals of a first course, with integration by parts. Their Mathlib form is in Volume 18. Only continuous functions on $[0, \pi]$ appear.

**Definition (Wallis integrals).** For $n \in \mathbb{N}$, put
$$I_n = \int_0^\pi \sin^n x \, dx.$$

**Definition (Wallis product).** For $k \in \mathbb{N}$, put
$$W_k = \prod_{i=1}^{k} \frac{2i}{2i - 1} \cdot \frac{2i}{2i + 1} = \frac{2}{1}\cdot\frac{2}{3}\cdot\frac{4}{3}\cdot\frac{4}{5}\cdots\frac{2k}{2k-1}\cdot\frac{2k}{2k+1}.$$
The empty product gives $W_0 = 1$.

**Definition (Stirling sequence).** For $n \ge 1$, put $s_n = \dfrac{n!}{\sqrt{2n}\,(n/e)^n}$.

The factor $\sqrt{2n}$ in place of $\sqrt{2\pi n}$ is the choice of Mathlib: the constant $\sqrt{\pi}$ is then the limit of $s_n$, and the proof finds it at the end.

::: mathlib
`Real.Wallis.W` · `Mathlib.Analysis.Real.Pi.Wallis`

The product `W k = ∏ i ∈ Finset.range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))`. The index runs over $0 \le i < k$, so the factor $i$ of Mathlib is the factor $i + 1$ of the text. The final result, `Real.tendsto_prod_pi_div_two`, states the limit with the product written out.

<?decl Real.Wallis.W?>
:::

::: mathlib
`Stirling.stirlingSeq` · `Mathlib.Analysis.SpecialFunctions.Stirling`

The sequence `stirlingSeq n = n ! / (√(2 * n) * (n / exp 1) ^ n)`, a function `ℕ → ℝ`. By the convention `x / 0 = 0`, `stirlingSeq 0 = 0`, so many lemmas of the file are stated for `n + 1` or with `n ≠ 0`.

<?decl Stirling.stirlingSeq?>
:::

### Theorems and proofs

**Lemma (Reduction formula).** $I_0 = \pi$, $I_1 = 2$, and $n I_n = (n - 1) I_{n-2}$ for $n \ge 2$.

*Proof.* $I_0 = \int_0^\pi 1\,dx = \pi$ and $I_1 = [-\cos x]_0^\pi = 2$. For $n \ge 2$, write $\sin^n x = \sin^{n-1} x \cdot \sin x$ and integrate by parts, with $u = \sin^{n-1} x$ and $v = -\cos x$:
$$I_n = \big[-\sin^{n-1} x \cos x\big]_0^\pi + (n - 1)\int_0^\pi \sin^{n-2} x \cos^2 x\,dx.$$
The bracket is $0$, since $\sin 0 = \sin \pi = 0$. With $\cos^2 = 1 - \sin^2$ the integral is $I_{n-2} - I_n$. So $I_n = (n - 1)(I_{n-2} - I_n)$, that is, $n I_n = (n - 1) I_{n-2}$. $\square$

**Corollary (Closed forms).** For $k \in \mathbb{N}$,
$$I_{2k} = \pi \prod_{i=1}^{k} \frac{2i - 1}{2i}, \qquad I_{2k+1} = 2 \prod_{i=1}^{k} \frac{2i}{2i + 1}, \qquad \frac{I_{2k+1}}{I_{2k}} = \frac{2}{\pi} W_k.$$

*Proof.* Induction on $k$ with the lemma: $I_{2k} = \frac{2k - 1}{2k} I_{2k-2}$ and $I_{2k+1} = \frac{2k}{2k+1} I_{2k-1}$. The quotient of the two products is $\frac{2}{\pi} \prod_{i=1}^k \frac{2i}{2i+1} \cdot \frac{2i}{2i-1} = \frac{2}{\pi} W_k$. $\square$

**Theorem (Wallis's product).** $\frac{2k+1}{2k+2} \cdot \frac{\pi}{2} \le W_k \le \frac{\pi}{2}$ for all $k$. In particular, $W_k \to \frac{\pi}{2}$:
$$\frac{\pi}{2} = \frac{2}{1}\cdot\frac{2}{3}\cdot\frac{4}{3}\cdot\frac{4}{5}\cdot\frac{6}{5}\cdot\frac{6}{7}\cdots.$$

*Proof.* For $x \in [0, \pi]$, $0 \le \sin x \le 1$, so $\sin^{n+1} x \le \sin^n x$. Integration preserves the inequality, so $I_{n+1} \le I_n$, and all $I_n$ are positive, since $\sin^n$ is continuous, nonnegative and positive at $\pi/2$. Then $I_{2k+2} \le I_{2k+1} \le I_{2k}$. Divide by $I_{2k}$ and use the lemma, $I_{2k+2} = \frac{2k+1}{2k+2} I_{2k}$:
$$\frac{2k+1}{2k+2} \le \frac{I_{2k+1}}{I_{2k}} = \frac{2}{\pi} W_k \le 1.$$
Multiply by $\frac{\pi}{2}$. The left side tends to $\frac{\pi}{2}$, so the squeeze theorem gives the limit. $\square$

**Lemma (Wallis's product with factorials).** $W_k = \dfrac{2^{4k} (k!)^4}{((2k)!)^2 (2k + 1)}$.

*Proof.* The numerators of $W_k$ give $\prod_{i=1}^k (2i)^2 = (2^k k!)^2$. The denominators give $\prod_{i=1}^k (2i - 1)(2i + 1) = \big(1 \cdot 3 \cdots (2k-1)\big)^2 (2k + 1)$. And $1 \cdot 3 \cdots (2k - 1) = \frac{(2k)!}{2 \cdot 4 \cdots 2k} = \frac{(2k)!}{2^k k!}$. So
$$W_k = \frac{(2^k k!)^2 (2^k k!)^2}{((2k)!)^2 (2k + 1)} = \frac{2^{4k}(k!)^4}{((2k)!)^2(2k+1)}. \qquad \square$$

::: mathlib
`Real.Wallis.tendsto_W_nhds_pi_div_two` · `Mathlib.Analysis.Real.Pi.Wallis`

The limit `Tendsto W atTop (𝓝 (π / 2))`. The proof in Mathlib is the proof above: `W_eq_integral_sin_pow_div_integral_sin_pow` is the corollary, `W_le` and `le_W` are the two bounds, and the squeeze theorem ends it. The integrals come from `integral_sin_pow_even`, `integral_sin_pow_odd` and `integral_sin_pow_antitone` of Volume 18, and the factorial form is `W_eq_factorial_ratio`.

<?decl Real.Wallis.tendsto_W_nhds_pi_div_two?>
:::

The first part of Stirling's formula needs the series of $\log \frac{1+y}{1-y}$.

**Lemma (A series for the logarithm).** For $0 \le y < 1$,
$$\log \frac{1 + y}{1 - y} = 2 \sum_{k=0}^{\infty} \frac{y^{2k+1}}{2k + 1}.$$

*Proof.* Fix $K \in \mathbb{N}$ and put $h(y) = \log(1 + y) - \log(1 - y) - 2\sum_{k=0}^{K} \frac{y^{2k+1}}{2k+1}$ for $0 \le y < 1$. Then $h(0) = 0$ and, with the geometric sum $\sum_{k=0}^{K} y^{2k} = \frac{1 - y^{2K+2}}{1 - y^2}$,
$$h'(y) = \frac{1}{1 + y} + \frac{1}{1 - y} - 2\sum_{k=0}^{K} y^{2k} = \frac{2}{1 - y^2} - \frac{2(1 - y^{2K+2})}{1 - y^2} = \frac{2 y^{2K+2}}{1 - y^2}.$$
For $0 < y < 1$ the mean value theorem gives $\eta \in (0, y)$ with $h(y) = h'(\eta)\,y$. So $0 \le h(y) \le \frac{2 y^{2K+3}}{1 - y^2}$, because $\eta < y$. As $K \to \infty$ the bound tends to $0$, since $y < 1$. $\square$

**Theorem (The Stirling sequence converges).** The sequence $(s_n)_{n \ge 1}$ is decreasing, and
$$0 \le \log s_n - \log s_{n+1} \le \frac{1}{12 n (n+1)}.$$
It converges to a limit $a$ with $a \ge \frac{e}{\sqrt 2}e^{-1/12} > 0$.

*Proof.* Step 1: the difference. From the definition, $\log s_n = \log n! - \frac12 \log(2n) - n \log n + n$. Subtract the same formula for $n + 1$ and use $\log (n+1)! = \log n! + \log(n + 1)$:
$$\log s_n - \log s_{n+1} = \left(n + \tfrac12\right)\log\left(1 + \tfrac1n\right) - 1.$$

Step 2: the series. Put $y = \frac{1}{2n+1}$. Then $\frac{1+y}{1-y} = \frac{2n+2}{2n} = 1 + \frac1n$ and $n + \frac12 = \frac{1}{2y}$. The lemma gives
$$\left(n + \tfrac12\right)\log\left(1 + \tfrac1n\right) = \frac{1}{2y} \cdot 2\sum_{k=0}^{\infty} \frac{y^{2k+1}}{2k+1} = 1 + \sum_{k=1}^{\infty} \frac{y^{2k}}{2k+1}.$$
So $\log s_n - \log s_{n+1} = \sum_{k \ge 1} \frac{y^{2k}}{2k+1}$. All terms are nonnegative, so the difference is $\ge 0$ and $s_n$ decreases.

Step 3: the upper bound. Each term is at most $\frac13 y^{2k}$, so the sum is at most $\frac13 \cdot \frac{y^2}{1 - y^2}$. Here $1 - y^2 = \frac{(2n+1)^2 - 1}{(2n+1)^2} = \frac{4n(n+1)}{(2n+1)^2}$, so $\frac{y^2}{1-y^2} = \frac{1}{4n(n+1)}$, and the bound is $\frac{1}{12n(n+1)}$.

Step 4: the lower bound. Sum Step 3 from $1$ to $n - 1$. The sum telescopes: $\frac{1}{12}\sum_{j=1}^{n-1}\left(\frac1j - \frac1{j+1}\right) = \frac{1}{12}\left(1 - \frac1n\right) < \frac1{12}$. So $\log s_1 - \log s_n < \frac{1}{12}$. With $s_1 = \frac{1}{\sqrt2 \,e^{-1}} = \frac{e}{\sqrt 2}$ this gives $s_n > \frac{e}{\sqrt2} e^{-1/12}$.

Step 5: a decreasing sequence that is bounded below converges, by the monotone convergence theorem of Chapter 1. Its limit $a$ satisfies the same lower bound. $\square$

::: mathlib
`Stirling.stirlingSeq_has_pos_limit_a` · `Mathlib.Analysis.SpecialFunctions.Stirling`

The statement `∃ a, 0 < a ∧ Tendsto stirlingSeq atTop (𝓝 a)`. The steps of the proof are lemmas of the file: `log_stirlingSeq_formula` (Step 1), `log_stirlingSeq_sdiff_hasSum` (Step 2), `log_stirlingSeq_sdiff_le` (Step 3), `stirlingSeq'_antitone` and `log_stirlingSeq_bounded_by_constant` (Step 4). The series lemma is `Real.hasSum_log_sub_log_of_abs_lt_one`.

<?decl Stirling.stirlingSeq_has_pos_limit_a?>
:::

**Theorem (The limit is $\sqrt{\pi}$).** $s_n \to \sqrt{\pi}$.

*Proof.* Step 1: an identity. For $n \ge 1$,
$$\frac{s_n^4}{s_{2n}^2} \cdot \frac{n}{2n + 1} = W_n.$$
Indeed, $s_n^4 = \frac{(n!)^4}{4n^2 (n/e)^{4n}}$ and $s_{2n}^2 = \frac{((2n)!)^2}{4n\,(2n/e)^{4n}}$. In the quotient the powers of $e$ cancel and $(2n)^{4n}/n^{4n} = 2^{4n}$, so
$$\frac{s_n^4}{s_{2n}^2} = \frac{(n!)^4 \cdot 4n \cdot 2^{4n}}{4n^2\,((2n)!)^2} = \frac{2^{4n}(n!)^4}{n\,((2n)!)^2}.$$
Multiply by $\frac{n}{2n+1}$ and compare with the factorial form of $W_n$.

Step 2: the limit. Let $a > 0$ be the limit of $s_n$. The subsequence $s_{2n}$ also tends to $a$, and $\frac{n}{2n+1} \to \frac12$. The rules for limits of Chapter 1, with $a \ne 0$, give $W_n \to \frac{a^4}{a^2} \cdot \frac12 = \frac{a^2}{2}$. By Wallis's product $W_n \to \frac{\pi}{2}$. Limits are unique, so $a^2 = \pi$, and $a = \sqrt\pi$ since $a > 0$. $\square$

**Theorem (Stirling's formula).** As $n \to \infty$,
$$n! \sim \sqrt{2\pi n}\left(\frac{n}{e}\right)^n.$$
Also, $\sqrt{2\pi n}\,(n/e)^n \le n! \le \sqrt{2\pi n}\,(n/e)^n\, e^{1/(12n)}$ for $n \ge 1$.

*Proof.* The quotient of the two sides is $\frac{n!}{\sqrt{2\pi n}(n/e)^n} = \frac{s_n}{\sqrt{\pi}}$, which tends to $1$. By the theorem on quotients of Section 1 this is the equivalence. For the bounds: $s_n$ decreases to $\sqrt\pi$, so $s_n \ge \sqrt{\pi}$, which is the lower bound. Sum Step 3 of the convergence theorem from $n$ to $m - 1$: $\log s_n - \log s_m \le \frac{1}{12}\left(\frac1n - \frac1m\right)$. Let $m \to \infty$: $\log s_n - \log\sqrt\pi \le \frac{1}{12n}$, which is the upper bound. $\square$

::: mathlib
`Stirling.factorial_isEquivalent_stirling` · `Mathlib.Analysis.SpecialFunctions.Stirling`

The formula `IsEquivalent atTop (fun n ↦ (n ! : ℝ)) fun n ↦ √(2 * n * π) * (n / exp 1) ^ n`. The limit of the theorem is `tendsto_stirlingSeq_sqrt_pi`, from `second_wallis_limit`, which is Step 2. The lower bound is `le_factorial_stirling`. The file is homed in Volume 19.

<?decl Stirling.factorial_isEquivalent_stirling?>
:::

### Examples

**Example (The table of values).** The table compares $n!$ with $S(n) = \sqrt{2\pi n}\,(n/e)^n$.

| $n$ | $n!$ | $S(n)$ | $n!/S(n)$ | $1 + \frac{1}{12n}$ | $s_n$ |
|---|---|---|---|---|---|
| $1$ | $1$ | $0.9221$ | $1.08444$ | $1.08333$ | $1.92212$ |
| $2$ | $2$ | $1.9190$ | $1.04221$ | $1.04167$ | $1.84726$ |
| $5$ | $120$ | $118.0192$ | $1.01678$ | $1.01667$ | $1.80220$ |
| $10$ | $3628800$ | $3598695.6$ | $1.00837$ | $1.00833$ | $1.78728$ |
| $100$ | $9.3326 \times 10^{157}$ | $9.3248 \times 10^{157}$ | $1.00083$ | $1.00083$ | $1.77393$ |

The ratio is always at least $1$, as the lower bound says, and it is close to $1 + \frac1{12n}$, which is the first term of $e^{1/(12n)}$. The sequence $s_n$ decreases to $\sqrt{\pi} = 1.77245$. The lower bound of the convergence theorem, $\frac{e}{\sqrt2}e^{-1/12} = 1.76843$, is close to the limit.

**Example (The central binomial coefficient).** By Stirling's formula and the product and quotient rules for $\sim$,
$$\binom{2n}{n} = \frac{(2n)!}{(n!)^2} \sim \frac{\sqrt{4\pi n}\,(2n/e)^{2n}}{2\pi n\,(n/e)^{2n}} = \frac{4^n}{\sqrt{\pi n}}.$$
For $n = 10$: $\binom{20}{10} = 184756$ and $4^{10}/\sqrt{10\pi} = 187079.0$, a ratio of $0.98758$. In probability, this says that the chance of exactly $n$ heads in $2n$ fair coin tosses is about $1/\sqrt{\pi n}$.

**Counterexample (Equivalence is not a good approximation of the difference).** Stirling's formula gives the relative error, not the absolute error. For $n = 10$ the difference $n! - S(n)$ is $30104$, and for $n = 100$ it is about $7.8 \times 10^{153}$. The difference tends to infinity, as in the common error $n^2 + n \sim n^2$ of Section 1.

### The library around it

The file `Mathlib.Analysis.Real.Pi.Wallis` has the namespace `Real.Wallis` with `W`, `W_pos`, `W_le`, `le_W`, `W_eq_factorial_ratio`, `W_eq_integral_sin_pow_div_integral_sin_pow` and `tendsto_W_nhds_pi_div_two`, and the final `Real.tendsto_prod_pi_div_two`. The file `Mathlib.Analysis.SpecialFunctions.Stirling` builds on it. The Gamma function of Volume 19 extends the factorial to real arguments.

Common errors of a learner:

- The formula is $n! \sim \sqrt{2\pi n}\,(n/e)^n$, with $n/e$, not $n \cdot e$, and with $\sqrt{2\pi n}$, not $\sqrt{2\pi}\, n$.
- $\sim$ is a statement on the ratio. It does not say that $n! - \sqrt{2\pi n}(n/e)^n$ is small, as the counterexample shows.
- In Mathlib, `stirlingSeq` divides by $\sqrt{2n}$, not by $\sqrt{2\pi n}$, so its limit is $\sqrt\pi$, not $1$. And `stirlingSeq 0 = 0`.
- The factorial in `factorial_isEquivalent_stirling` is cast to `ℝ`: `(n ! : ℝ)`. A goal with the natural number `n !` needs `Nat.cast` first.
- Wallis's product in Mathlib starts at $i = 0$ with the factors $\frac{2}{1}\cdot\frac{2}{3}$, so the index is shifted by one from the text.

### Exercises

1. (A) Compute $W_1, W_2, W_3$ and compare with $\pi/2 = 1.5708$. Check the bounds $\frac{2k+1}{2k+2}\cdot\frac{\pi}{2} \le W_k \le \frac{\pi}{2}$ for $k = 3$.
2. (A) Use the two-sided bound to compute $20!$ to $3$ significant digits, and compare with $20! = 2432902008176640000$.
3. (A) Prove that $\left(n!\right)^{1/n} \sim \frac{n}{e}$. Hint: $(2\pi n)^{1/(2n)} \to 1$.
4. (B) Prove that $\frac{(2n)!}{4^n (n!)^2} \sim \frac{1}{\sqrt{\pi n}}$, and deduce that $\sum_n \frac{(2n)!}{4^n (n!)^2}$ diverges.
5. (B) Prove that $\log s_n - \log s_{n+1} \ge \frac{1}{3(2n+1)^2} \ge \frac{1}{12n + 1} - \frac{1}{12(n+1) + 1}$ for $n \ge 1$. Deduce the lower bound $n! \ge \sqrt{2\pi n}\,(n/e)^n e^{1/(12n+1)}$. Hint: keep only the first term of the series, then sum the telescoping bound from $n$ to infinity.
6. (C) Prove $I_n \sim \sqrt{\frac{2\pi}{n}}$ as $n \to \infty$. Hint: show that $n I_n I_{n-1} = 2\pi$ with the reduction formula, and use $I_{n+1} \le I_n \le I_{n-1}$.

### Notes and history

John Wallis found his product in 1655, in *Arithmetica infinitorum*. Abraham de Moivre found in 1730 that $n! \approx C\sqrt{n}\,(n/e)^n$, and James Stirling identified $C = \sqrt{2\pi}$ in the same year, with the help of Wallis's product. The bound of Exercise 5 is due to Herbert Robbins (1955). In Mathlib, Wallis's product was formalized by Hanting Zhang (2021), and Stirling's formula by Moritz Firsching, Fabian Kruse and Nikolas Kuhn (2022).

### Reference

<?reference?>
