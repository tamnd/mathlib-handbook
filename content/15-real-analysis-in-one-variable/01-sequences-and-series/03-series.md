---
title: Series
kind: theory
modules:
  - Mathlib.Analysis.PSeries
  - Mathlib.Analysis.SpecificLimits.Normed
explains:
  E3: [summable_condensed_iff_of_nonneg, Real.summable_nat_rpow_inv, summable_of_ratio_test_tendsto_lt_one, Antitone.tendsto_alternating_series_of_tendsto_zero]
  E2: [summable_geometric_of_lt_one, tsum_geometric_of_lt_one, hasSum_geometric_of_lt_one, summable_geometric_of_abs_lt_one, tsum_geometric_of_abs_lt_one, summable_geometric_iff_norm_lt_one, Real.summable_one_div_nat_rpow, Real.summable_nat_pow_inv, Real.summable_one_div_nat_pow, Real.not_summable_natCast_inv, Real.not_summable_one_div_natCast, Real.tendsto_sum_range_one_div_nat_succ_atTop, Finset.sum_condensed_le, Finset.le_sum_condensed, summable_of_ratio_norm_eventually_le, not_summable_of_ratio_test_tendsto_gt_one, Real.summable_pow_div_factorial, Antitone.cauchySeq_alternating_series_of_tendsto_zero, alternating_series_error_bound]
  E1: auto
families: []
requires: [V02, V13]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Series

### Overview

The sum $\sum_{n=0}^{\infty} a_n$ is the limit of the partial sums $S_N = a_0 + \cdots + a_{N-1}$, when the limit exists. So the criteria of Sections 1 and 2 apply to series. This section proves the comparison test, the ratio test, the Cauchy condensation test with the $p$-series $\sum 1/n^p$, absolute convergence and the alternating series test of Leibniz.

Mathlib takes another definition. Its sum `tsum` is an *unconditional* sum, a limit over finite sets of indices in any order. For a real series, the unconditional sum exists exactly when the series converges absolutely. So $1 - \tfrac12 + \tfrac13 - \cdots$ converges in the sense of the textbooks, and it is not `Summable` in Mathlib.

### Definitions

**Definition (Convergent series).** Let $(a_n)_{n \ge 0}$ be real, with partial sums $S_N = \sum_{n=0}^{N-1} a_n$. The series $\sum a_n$ *converges* to $s$ if $S_N \to s$, and then $s$ is its *sum*. Otherwise the series *diverges*. It *converges absolutely* if $\sum |a_n|$ converges, and *conditionally* if it converges and does not converge absolutely.

**Definition (Unconditional sum).** A sequence $f : \mathbb{N} \to \mathbb{R}$ has *unconditional sum* $s$ if for each $\varepsilon > 0$ there is a finite set $F_0 \subseteq \mathbb{N}$ such that $\left| \sum_{i \in F} f(i) - s \right| < \varepsilon$ for each finite $F \supseteq F_0$.

If $\sigma$ is a bijection of $\mathbb{N}$, then $f \circ \sigma$ has the same unconditional sum: take $\sigma^{-1}(F_0)$ in place of $F_0$.

::: mathlib
`HasSum` · `Mathlib.Topology.Algebra.InfiniteSum.Defs`

`HasSum f a` says that `fun s : Finset ι => ∑ i ∈ s, f i` tends to `a` along the filter `atTop` of finite sets ordered by inclusion. This is the unconditional sum. `Summable f` says that some such `a` exists, and `∑' i, f i` is that `a`, or the junk value `0` if `f` is not summable (`tsum_eq_zero_of_not_summable`). The three take an optional `SummationFilter`, with the default `SummationFilter.unconditional`; `SummationFilter.conditional` gives the partial sums over intervals, the convergence of the textbooks. Mathlib chose this default because it works for each index type and the rules for sums need no extra hypothesis. Volume 14 develops it.

<?decl HasSum?>
:::

### Theorems and proofs

**Theorem (Terms tend to zero).** If $\sum a_n$ converges, then $a_n \to 0$.

*Proof.* If $S_N \to s$, then $S_{N+1} \to s$, and $a_N = S_{N+1} - S_N \to 0$. $\square$

**Theorem (Geometric series).** If $|r| < 1$, then $\sum_{n=0}^{\infty} r^n = \dfrac{1}{1 - r}$. If $|r| \ge 1$, the series diverges.

*Proof.* For $r \ne 1$, $(1 - r) S_N = 1 - r^N$, so $S_N = (1 - r^N)/(1 - r)$. If $|r| < 1$, then $r^N \to 0$ and $S_N \to 1/(1 - r)$. If $|r| \ge 1$, the terms do not tend to $0$. $\square$

::: mathlib
`summable_geometric_of_lt_one` · `Mathlib.Analysis.SpecificLimits.Basic`

The case $0 \le r < 1$, with the sum `tsum_geometric_of_lt_one` and the form `hasSum_geometric_of_lt_one`. A negative ratio is `summable_geometric_of_abs_lt_one` with `tsum_geometric_of_abs_lt_one`, and the criterion in a normed field is `summable_geometric_iff_norm_lt_one`.

<?decl summable_geometric_of_lt_one?>
:::

**Theorem (Comparison test).** A series of nonnegative terms converges if and only if its partial sums are bounded. If $0 \le a_n \le b_n$ and $\sum b_n$ converges, then $\sum a_n$ converges and $\sum a_n \le \sum b_n$.

*Proof.* If $a_n \ge 0$, then $S_{N+1} = S_N + a_N \ge S_N$, so $(S_N)$ is increasing, and the monotone convergence theorem of Section 2 gives the first claim. For the second, $\sum_{n<N} a_n \le \sum_{n<N} b_n \le \sum_{n=0}^{\infty} b_n$, so the partial sums of $\sum a_n$ are bounded. Limits keep $\le$. $\square$

::: mathlib
`Summable.of_nonneg_of_le` · `Mathlib.Topology.Algebra.InfiniteSum.ENNReal`

The comparison test for real families. The criterion with bounded partial sums is `summable_of_sum_range_le`. For nonnegative terms, `hasSum_iff_tendsto_nat_of_nonneg` says that the unconditional sum is the limit of the partial sums.

<?decl Summable.of_nonneg_of_le?>
:::

**Theorem (Cauchy condensation).** Let $(a_n)_{n \ge 1}$ be nonnegative and decreasing. Then $\sum_{n \ge 1} a_n$ converges if and only if $\sum_{k \ge 0} 2^k a_{2^k}$ converges.

*Proof.* Put $S_N = \sum_{n=1}^{N} a_n$ and $T_K = \sum_{k=0}^{K} 2^k a_{2^k}$. Both are increasing, so it is enough to show that one is bounded if and only if the other is.

Split $1, \ldots, 2^{K+1} - 1$ into the blocks $\{2^k, \ldots, 2^{k+1} - 1\}$ for $k = 0, \ldots, K$. Each block has $2^k$ elements, with $a_n \le a_{2^k}$ on it. So $S_{2^{K+1} - 1} \le T_K$.

Split $2, \ldots, 2^K$ into the blocks $\{2^{k-1} + 1, \ldots, 2^k\}$ for $k = 1, \ldots, K$. Each block has $2^{k-1}$ elements, with $a_n \ge a_{2^k}$ on it. So
$$S_{2^K} - a_1 \ge \sum_{k=1}^{K} 2^{k-1} a_{2^k} = \tfrac{1}{2}\left(T_K - a_1\right).$$

If $T_K \le M$ for all $K$, then $S_N \le S_{2^{N+1}-1} \le T_N \le M$. If $S_N \le M$ for all $N$, then $T_K \le 2 S_{2^K} - a_1 \le 2M$. $\square$

::: mathlib
`summable_condensed_iff_of_nonneg` · `Mathlib.Analysis.PSeries`

The theorem for a real sequence indexed from $0$. The hypothesis of decrease is `∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m`, so `f 0` plays no part. The two block estimates are `Finset.sum_condensed_le` and `Finset.le_sum_condensed`.

<?decl summable_condensed_iff_of_nonneg?>
:::

**Theorem ($p$-series).** The series $\sum_{n \ge 1} 1/n^p$ converges if and only if $p > 1$. In particular the harmonic series $\sum 1/n$ diverges.

*Proof.* If $p \le 0$, then $1/n^p \ge 1$ and the terms do not tend to $0$. Let $p > 0$. Then $n^{-p}$ is positive and decreasing, and the condensed series is
$$\sum_{k \ge 0} 2^k (2^k)^{-p} = \sum_{k \ge 0} \left(2^{1-p}\right)^k,$$
a geometric series. It converges if and only if $2^{1-p} < 1$, that is $p > 1$. $\square$

::: mathlib
`Real.summable_nat_rpow_inv` · `Mathlib.Analysis.PSeries`

The statement `Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) ↔ 1 < p`, with the real power of Chapter 5. The forms with `1 / n ^ p` and natural exponents are `Real.summable_one_div_nat_rpow`, `Real.summable_nat_pow_inv` and `Real.summable_one_div_nat_pow`. The harmonic series is `Real.not_summable_natCast_inv` and `Real.not_summable_one_div_natCast`, and `Real.tendsto_sum_range_one_div_nat_succ_atTop` says that its partial sums tend to infinity.

<?decl Real.summable_nat_rpow_inv?>
:::

**Theorem (Ratio test).** Let $a_n \ne 0$ for large $n$, and $|a_{n+1}| / |a_n| \to \rho$. If $\rho < 1$, then $\sum |a_n|$ converges. If $\rho > 1$, then $\sum a_n$ diverges.

*Proof.* Let $\rho < r < 1$. There is $N$ with $|a_{n+1}| \le r |a_n|$ for $n \ge N$, so $|a_n| \le |a_N| r^{n - N}$ for $n \ge N$. By comparison with a geometric series, $\sum_{n \ge N} |a_n|$ converges, and the first $N$ terms do not change convergence. If $\rho > 1$, then eventually $|a_{n+1}| \ge |a_n|$, so $|a_n| \ge |a_N| > 0$ for $n \ge N$, and the terms do not tend to $0$. $\square$

For $\rho = 1$ the test gives no answer: $\sum 1/n$ diverges and $\sum 1/n^2$ converges.

::: mathlib
`summable_of_ratio_test_tendsto_lt_one` · `Mathlib.Analysis.SpecificLimits.Normed`

The ratio test in a complete normed group, with the hypotheses `l < 1`, `∀ᶠ n in atTop, f n ≠ 0` and the limit of `‖f (n + 1)‖ / ‖f n‖`. The form with an eventual bound `‖f (n + 1)‖ ≤ r * ‖f n‖` is `summable_of_ratio_norm_eventually_le`, and the divergence part is `not_summable_of_ratio_test_tendsto_gt_one`.

<?decl summable_of_ratio_test_tendsto_lt_one?>
:::

**Theorem (Absolute convergence).** If $\sum |a_n|$ converges, then $\sum a_n$ converges, and $\left|\sum a_n\right| \le \sum |a_n|$.

*Proof.* The partial sums of $\sum |a_n|$ are Cauchy, so for $\varepsilon > 0$ there is $N$ with $\sum_{k=n}^{m-1} |a_k| < \varepsilon$ for $m > n \ge N$. Then $|S_m - S_n| \le \sum_{k=n}^{m-1} |a_k| < \varepsilon$. So $(S_N)$ is Cauchy and converges. The bound $|S_N| \le \sum |a_n|$ passes to the limit. $\square$

**Theorem (Unconditional and absolute summability).** A sequence $f : \mathbb{N} \to \mathbb{R}$ has an unconditional sum if and only if $\sum f(n)$ converges absolutely. The two sums agree.

*Proof.* Let $\sum |f(n)|$ converge, and let $s$ be the sum of $\sum f(n)$. For $\varepsilon > 0$ choose $N$ with $\sum_{n \ge N} |f(n)| < \varepsilon$, and put $F_0 = \{0, \ldots, N-1\}$. For a finite $F \supseteq F_0$, $\left|\sum_{F} f - S_N\right| \le \sum_{n \in F \setminus F_0} |f(n)| < \varepsilon$, and $|S_N - s| \le \varepsilon$. So $\sum_F f$ is within $2\varepsilon$ of $s$.

Conversely, let $f$ have unconditional sum $s$, and choose $F_0$ for $\varepsilon = 1$. For each finite $G$ disjoint from $F_0$, $\left|\sum_{G} f\right| = \left|\sum_{F_0 \cup G} f - \sum_{F_0} f\right| < 2$. Apply this to the indices $G^+$ in $G$ with $f > 0$ and $G^-$ with $f < 0$: then $\sum_{G} |f| = \sum_{G^+} f - \sum_{G^-} f < 4$. So the partial sums of $\sum |f(n)|$ are bounded by $4 + \sum_{F_0} |f|$, and the series converges. $\square$

::: mathlib
`summable_abs_iff` · `Mathlib.Topology.Algebra.InfiniteSum.Order`

The theorem `(Summable fun x => |f x|) ↔ Summable f` in each complete linearly ordered additive group. The direction from left to right holds in each complete normed group, as `Summable.of_norm`.

<?decl summable_abs_iff?>
:::

**Theorem (Leibniz test).** Let $(b_n)_{n \ge 0}$ decrease to $0$. Then $\sum_{n \ge 0} (-1)^n b_n$ converges to some $L$, and $|S_N - L| \le b_N$ for each $N$.

*Proof.* Since $b_n$ decreases to $0$, $b_n \ge 0$. Then
$$S_{2m+2} = S_{2m} + (b_{2m} - b_{2m+1}) \ge S_{2m}, \qquad S_{2m+3} = S_{2m+1} - (b_{2m+1} - b_{2m+2}) \le S_{2m+1},$$
and $S_{2m+1} = S_{2m} + b_{2m} \ge S_{2m}$. So $S_0 \le S_{2m} \le S_{2m+1} \le S_1$. By monotone convergence $S_{2m} \to L$ and $S_{2m+1} \to L'$, and $L' - L = \lim b_{2m} = 0$. So $S_N \to L$. The even sums increase to $L$ and the odd sums decrease to $L$, so $L$ lies between $S_N$ and $S_{N+1}$, and $|S_N - L| \le |S_{N+1} - S_N| = b_N$. $\square$

::: mathlib
`Antitone.tendsto_alternating_series_of_tendsto_zero` · `Mathlib.Analysis.SpecificLimits.Normed`

The Leibniz test as `∃ l, Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l)`. The conclusion is a limit of partial sums and not `Summable`, since a conditionally convergent series has no unconditional sum. The Cauchy form is `Antitone.cauchySeq_alternating_series_of_tendsto_zero`, and the error bound is `alternating_series_error_bound`.

<?decl Antitone.tendsto_alternating_series_of_tendsto_zero?>
:::

### Examples

**Counterexample (The harmonic series).** The terms $1/n$ tend to $0$, and the series diverges. Directly: $\sum_{k=n+1}^{2n} \frac1k \ge n \cdot \frac{1}{2n} = \frac12$, so $H_{2^m} \ge 1 + \frac{m}{2}$, where $H_N = \sum_{k=1}^{N} \frac1k$. The growth is slow: $H_N > 10$ first holds at $N = 12367$.

**Example (The exponential series).** Let $x \ne 0$ and $a_n = x^n / n!$. Then $|a_{n+1}|/|a_n| = |x|/(n+1) \to 0$, so $\sum x^n / n!$ converges absolutely by the ratio test (`Real.summable_pow_div_factorial`). For $x = 1$ the partial sums are $1, 2, 2.5, 2.6667, 2.7083, 2.7167$.

**Example (The alternating harmonic series).** Let $b_n = \frac{1}{n+1}$. By the Leibniz test $1 - \frac12 + \frac13 - \cdots$ converges to some $L$. The partial sums are $1, \frac12, \frac56, \frac{7}{12}, \frac{47}{60}$, and $|S_4 - L| \le \frac15$ with $S_4 = \frac{7}{12}$ gives $0.383 \le L \le 0.784$. Chapter 5 shows $L = \log 2 \approx 0.6931$. The convergence is conditional. In Mathlib, `Summable (fun n : ℕ => (-1 : ℝ) ^ n / (n + 1))` is false, and its `tsum` is the junk value `0`. A rearrangement with two positive terms after each negative one converges to $\frac32 \log 2$; Riemann proved that a conditionally convergent series can be rearranged to any sum.

### The library around it

`Mathlib.Analysis.SpecificLimits.Basic` gives the geometric series, `Mathlib.Analysis.SpecificLimits.Normed` the ratio and alternating tests, and `Mathlib.Analysis.PSeries` the condensation test and the $p$-series. To pass between the two definitions: `HasSum.tendsto_sum_nat` gives the partial sums from `HasSum`; `hasSum_iff_tendsto_nat_of_nonneg` gives `HasSum` from the partial sums for nonnegative terms; `summable_nat_add_iff` drops finitely many terms. For a conditionally convergent series, use `Tendsto` of the partial sums or `HasSum f a (SummationFilter.conditional ℕ)`.

Common errors of a learner:

- `∑' n, f n` has a value even when the series diverges. The junk value makes `∑' n : ℕ, (1 : ℝ) / (n + 1) = 0` true. Prove `Summable f` first.
- `Summable` is not the textbook convergence: it fails for the alternating harmonic series.
- In `fun n : ℕ => 1 / (n : ℝ) ^ p`, the term at `n = 0` is `0`, not infinity. Without the cast, `1 / n` is `0` for `n ≥ 2`.

### Exercises

1. (A) Compute $\sum_{n=0}^{\infty} \frac{2^n + 3^n}{6^n}$.
2. (A) Show that $\sum_{n \ge 1} \frac{n}{n^2 + 1}$ diverges. Hint: compare with $\frac{1}{2n}$.
3. (A) Show that $\sum_{n \ge 1} \frac{1}{n(n+1)} = 1$ and deduce $\sum_{n \ge 1} \frac{1}{n^2} \le 2$. Hint: telescope.
4. (B) Show that $\sum_{n \ge 2} \frac{1}{n \log n}$ diverges and $\sum_{n \ge 2} \frac{1}{n (\log n)^2}$ converges. Hint: condensation.
5. (B) Give a convergent series $\sum a_n$ with $\sum a_n^2$ divergent. Hint: an alternating series.
6. (B) How many terms of $\sum_{n \ge 0} \frac{(-1)^n}{2n + 1} = \frac{\pi}{4}$ give an error less than $10^{-3}$ by the Leibniz bound?
7. (C) Prove the root test: if $\limsup |a_n|^{1/n} < 1$, then $\sum |a_n|$ converges. Give a series where it applies and the ratio test does not. Hint: $a_n = 2^{-n}$ for $n$ even and $3^{-n}$ for $n$ odd.

### Notes and history

Oresme proved the divergence of the harmonic series around 1350. Leibniz stated the alternating series test in letters from 1705. Cauchy treated convergence systematically in the *Cours d'analyse* of 1821, with the ratio, root and condensation tests. Riemann proved the rearrangement theorem in 1854. The unconditional sum is from Bourbaki.

### Reference

<?reference?>
