---
title: Specific limits, subadditive sequences and sums against integrals
kind: api
modules:
  - Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
  - Mathlib.Analysis.SpecificLimits.Fibonacci
  - Mathlib.Analysis.SpecificLimits.FloorPow
  - Mathlib.Analysis.SpecificLimits.RCLike
  - Mathlib.Analysis.Subadditive
  - Mathlib.Analysis.SumIntegralComparisons
  - Mathlib.Analysis.SumIntegralExpDecay
explains:
  E2: [arithGeom_eq, tendsto_arithGeom_nhds_of_lt_one, tendsto_fib_succ_div_fib_atTop, mul_pow_le_nat_floor_pow, Subadditive.tendsto_lim, AntitoneOn.integral_le_sum, AntitoneOn.sum_le_integral, AntitoneOn.summable_of_integrableOn_Ioi]
  E1: auto
families: []
requires: [V02, V13, V18]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Specific limits, subadditive sequences and sums against integrals

### Overview

The first three sections of this chapter give the general theory of limits, of monotone and Cauchy sequences, and of series. This section collects tools for concrete sequences. The modules hold four kinds of results. The first kind computes the limits of two classical recurrences: the arithmetic-geometric sequence $u_{n+1} = a u_n + b$ and the ratio of consecutive Fibonacci numbers. The second kind is Fekete's lemma: for a subadditive sequence, $u_n / n$ converges. The third kind compares a sum $\sum f(n)$ with an integral $\int f$ for a monotone function $f$. This comparison gives the integral test for series. The fourth kind is a set of technical results on the sequence $\lfloor c^n \rfloor$, which the proof of the strong law of large numbers uses.

The integral comparisons use the interval integral `∫ x in a..b, f x` and the predicate `MeasureTheory.IntegrableOn` of the volume on measure and integration. A reader needs only the facts that the integral is monotone and that $\int_n^{n+1} c \, dx = c$ for a constant $c$.

### The library around it

#### Arithmetic-geometric sequences

The module `Mathlib.Analysis.SpecificLimits.ArithmeticGeometric` defines `arithGeom a b u₀ : ℕ → R` by recursion: `arithGeom_zero` gives the value $u_0$ at $0$ and `arithGeom_succ` gives $u_{n+1} = a u_n + b$. The definition needs only a multiplication and an addition on `R`. The closed forms need more structure. In a commutative semiring, `arithGeom_eq_add_sum` states $u_n = a^n u_0 + b \sum_{k < n} a^k$. In a field, with $a \ne 1$, the sum is a geometric sum, and the sequence has a closed form.

**Theorem.** Let $a \ne 1$ and $\ell = b / (1 - a)$. Then $u_n = a^n (u_0 - \ell) + \ell$ for all $n$.

*Proof.* The number $\ell$ is the fixed point of $x \mapsto a x + b$, because $a \ell + b = \ell$. Subtract this equation from $u_{n+1} = a u_n + b$. Then $u_{n+1} - \ell = a (u_n - \ell)$. Induction on $n$ gives $u_n - \ell = a^n (u_0 - \ell)$. $\square$

This is `arithGeom_eq`, and `arithGeom_eq'` is the same statement as an equation of functions. The special starting values $u_0 = 0$ and $u_0 = b$ have their own lemmas: `arithGeom_zero_eq_sum`, `arithGeom_zero_eq_mul_div`, `arithGeom_same_eq_sum` and `arithGeom_same_eq_mul_div`. The variants with a prime write the quotient with $1 - a$ in the denominator instead of $a - 1$.

The limits follow from the closed form. In an Archimedean ordered field with the order topology, `tendsto_arithGeom_nhds_of_lt_one` states that $u_n \to b / (1 - a)$ when $0 \le a < 1$. The proof: $a^n \to 0$ by the limit of a geometric sequence, so $a^n (u_0 - \ell) + \ell \to \ell$. For $a > 1$ and $u_0 > \ell$, the factor $u_0 - \ell$ is positive and $a^n \to \infty$, so $u_n \to \infty$: this is `tendsto_arithGeom_atTop_of_one_lt`. Under the same hypotheses `arithGeom_strictMono` states that the sequence is strictly increasing, and `div_lt_arithGeom` (with $a > 0$) states that every term stays above $\ell$.

#### The Fibonacci ratio

The module `Mathlib.Analysis.SpecificLimits.Fibonacci` has two theorems about `Nat.fib`. The first, `tendsto_fib_succ_div_fib_atTop`, states $F_{n+1} / F_n \to \varphi$, where $\varphi = (1 + \sqrt 5)/2$ is `Real.goldenRatio`. The second, `tendsto_fib_div_fib_succ_atTop`, states $F_n / F_{n+1} \to -\psi$, where $\psi = (1 - \sqrt 5)/2$ is `Real.goldenConj`. Note that $-\psi = 1/\varphi$.

*Proof sketch.* Binet's formula gives $F_n = (\varphi^n - \psi^n)/\sqrt 5$. Divide the numerator and the denominator of $F_{n+1}/F_n$ by $\varphi^n$. The quotient becomes $(\varphi - \psi r^n)/(1 - r^n)$ with $r = \psi/\varphi$. Since $|r| < 1$, $r^n \to 0$, and the quotient tends to $\varphi$. $\square$

#### Subadditive and submultiplicative sequences

The module `Mathlib.Analysis.Subadditive` defines `Subadditive u` for a function $u$ with $u(m + n) \le u(m) + u(n)$ for all $m, n$, and `Submultiplicative u` for $u(m + n) \le u(m) u(n)$. The additive notion is the image of the multiplicative one under the attribute `to_additive`, so each lemma exists in the two forms. For $u : \mathbb{N} \to \mathbb{R}$ the module defines a candidate limit `Subadditive.lim`, the infimum of $u_n / n$ over $n \ge 1$, and `Submultiplicative.lim`, the infimum of $u_n^{1/n}$ over $n \ge 1$.

**Theorem (Fekete).** Let $u$ be subadditive and let $u_n / n$ be bounded below. Then $u_n / n$ converges to $L = \inf_{n \ge 1} u_n / n$.

*Proof.* By definition $L \le u_m / m$ for every $m \ge 1$ (`Subadditive.lim_le_div`). Fix $n \ge 1$. Write $m = k n + r$ with $0 \le r < n$. Subadditivity, applied $k$ times, gives $u_m \le k u_n + u_r$ (`Subadditive.apply_mul_add_le`). Divide by $m$:
$$\frac{u_m}{m} \le \frac{k n}{m} \cdot \frac{u_n}{n} + \frac{u_r}{m}.$$
As $m \to \infty$, $kn/m \to 1$, and $u_r / m \to 0$ because $u_r$ takes only $n$ values. So eventually $u_m / m < u_n / n + \varepsilon$. Choose $n$ with $u_n / n < L + \varepsilon$. Then eventually $L \le u_m / m < L + 2\varepsilon$. $\square$

This is `Subadditive.tendsto_lim`. The middle step, "eventually $u_m / m < L'$ when $u_n/n < L'$ for one $n$", is `Subadditive.eventually_div_lt_of_div_lt`. The multiplicative versions are `Submultiplicative.tendsto_lim`, `Submultiplicative.lim_le_rpow`, `Submultiplicative.apply_mul_add_le` and `Submultiplicative.eventually_rpow_lt_of_rpow_lt`. They need $u_n \ge 0$ instead of a lower bound. `Subadditive.submultiplicative_exp` states that $e^{u_n}$ is submultiplicative when $u$ is subadditive. A typical application is the spectral radius formula $\lim \|T^n\|^{1/n}$, since $\|T^{m+n}\| \le \|T^m\| \|T^n\|$.

#### Discretized exponentials

The module `Mathlib.Analysis.SpecificLimits.FloorPow` treats the sequence $\lfloor c^n \rfloor_+$ for a real $c > 1$, written `⌊c ^ n⌋₊` with the natural floor. The first fact is a lower bound: `mul_pow_le_nat_floor_pow` states $(1 - c^{-1}) c^i \le \lfloor c^i \rfloor_+$.

*Proof.* For $i = 0$ the left side is $1 - c^{-1} < 1 = \lfloor 1 \rfloor_+$. For $i \ge 1$, $c^{i-1} \ge 1$, so $(1 - c^{-1}) c^i = c^i - c^{i-1} \le c^i - 1 < \lfloor c^i \rfloor_+$. $\square$

The main theorem is a criterion for the convergence of $u_n / n$ for a monotone sequence $u$. `tendsto_div_of_monotone_of_exists_subseq_tendsto_div` states: if for every $a > 1$ there is a sequence $c_n \to \infty$ with $c_{n+1} \le a c_n$ eventually and $u_{c_n} / c_n \to l$, then $u_n / n \to l$. The proof squeezes $n$ between $c_k$ and $c_{k+1}$ and uses the monotonicity of $u$. The special case `tendsto_div_of_monotone_of_tendsto_div_floor_pow` uses $c_n = \lfloor c_k^n \rfloor_+$ for a sequence $c_k \to 1$. The two sums `sum_div_pow_sq_le_div_sq` and `sum_div_nat_floor_pow_sq_le_div_sq` bound $\sum 1/(c^i)^2$ and $\sum 1/\lfloor c^i \rfloor_+^2$ over the indices with $c^i > j$ by a constant times $1/j^2$.

#### Real numbers inside an `RCLike` field

The module `Mathlib.Analysis.SpecificLimits.RCLike` has three limits for the embedding `RCLike.ofReal` of $\mathbb{R}$ into $\mathbb{R}$ or $\mathbb{C}$. The filter `Bornology.cobounded 𝕜` is the filter of complements of bounded sets: a function tends to it when its norm tends to infinity. `RCLike.tendsto_ofReal_atTop_cobounded`, `RCLike.tendsto_ofReal_atBot_cobounded` and `RCLike.tendsto_ofReal_cobounded_cobounded` state that a real number that tends to $+\infty$, to $-\infty$ or to infinity in absolute value also tends to infinity in `𝕜`.

#### Sums against integrals

The module `Mathlib.Analysis.SumIntegralComparisons` compares $\sum f(i)$ with $\int f$ for a monotone function. The basic picture: on $[x_0 + i, x_0 + i + 1]$ an antitone function satisfies $f(x_0 + i + 1) \le f(x) \le f(x_0 + i)$.

**Theorem.** Let $f$ be antitone on $[x_0, x_0 + a]$. Then
$$\sum_{i < a} f(x_0 + i + 1) \le \int_{x_0}^{x_0 + a} f(x)\,dx \le \sum_{i < a} f(x_0 + i).$$

*Proof.* A monotone function on a compact interval is integrable. Integrate the inequality $f(x_0 + i + 1) \le f(x) \le f(x_0 + i)$ over $[x_0 + i, x_0 + i + 1]$, an interval of length $1$. Then sum over $i < a$ and use the additivity of the integral over adjacent intervals. $\square$

The two halves are `AntitoneOn.sum_le_integral` and `AntitoneOn.integral_le_sum`. The library has the same results for monotone functions with the inequalities reversed (`MonotoneOn.sum_le_integral`, `MonotoneOn.integral_le_sum`), and versions over `Finset.Ico a b` with integer end points (`AntitoneOn.integral_le_sum_Ico`, `AntitoneOn.sum_le_integral_Ico`, `MonotoneOn.sum_le_integral_Ico`, `MonotoneOn.integral_le_sum_Ico`). The names with `_of_integrableOn` replace the monotonicity on the closed interval by a weaker hypothesis on a half-open interval plus integrability. The general forms `sum_Ico_le_integral_of_le` and `integral_le_sum_Ico_of_le` compare a step function with a function $g$ directly, and `sum_mul_Ico_le_integral_of_monotone_antitone` and `integral_le_sum_mul_Ico_of_antitone_monotone` treat a product of an antitone and a monotone function.

On the half line $(0, \infty)$ the comparisons become the integral test. For $f \ge 0$ antitone on $[N, \infty)$:

| Lean name | Statement |
|---|---|
| `AntitoneOn.summable_of_integrableOn_Ioi` | $f$ integrable on $(N, \infty)$ implies $\sum f(n)$ converges |
| `AntitoneOn.integrableOn_Ioi_of_summable_comp_add` | $\sum f(n + N)$ converges implies $f$ integrable on $(N, \infty)$ |
| `AntitoneOn.tsum_le_integral` | $\sum_{n \ge 0} f(n) \le f(0) + \int_0^\infty f$ |
| `AntitoneOn.integral_le_tsum` | $\int_0^\infty f \le \sum_{n \ge 0} f(n)$ |
| `AntitoneOn.abs_tsum_sub_sum_range_le_integral` | $\left|\sum_{n} f(n) - \sum_{n < N} f(n)\right| \le \int_{N-1}^\infty f$ |

The last row bounds the tail of a series by an integral. With $f(x) = x^{-p}$ it gives the error of a partial sum of the series $\sum n^{-p}$ of the section on series.

The module `Mathlib.Analysis.SumIntegralExpDecay` applies the comparison to $x^k e^{-cx}$. `intervalIntegral_pow_mul_exp_neg_le` states $\int_0^M x^k e^{-cx}\,dx \le k!/c^{k+1}$, by comparison with the Gamma integral. The sums `sum_Ico_pow_mul_exp_neg_le` and `sum_Iic_pow_mul_exp_neg_le` bound $\sum_{i \le M} i^k e^{-ci}$ by $e^c k!/c^{k+1}$, and `sum_Iic_pow_mul_two_pow_neg_le` is the same bound with base $2$.

#### Common errors

1. Forgetting the hypothesis of `Subadditive.tendsto_lim`. Without a lower bound on $u_n / n$ the infimum `Subadditive.lim` is the junk value of the infimum of a set that is not bounded below, and the theorem does not apply. The sequence $u_n = -n^2$ is subadditive and $u_n / n \to -\infty$.
2. Using `AntitoneOn.summable_of_integrableOn_Ioi` without the sign condition. The comparison needs $f \ge 0$ on the half line, because integrability on $(N, \infty)$ in the sense of Lebesgue is a statement about $|f|$.
3. Reading `⌊c ^ n⌋₊` as the integer floor. It is `Nat.floor`, with value in $\mathbb{N}$; the lemmas cast it back to $\mathbb{R}$, and a goal often shows the cast `↑⌊c ^ n⌋₊`.

### Exercises

1. (A) Use `arithGeom_eq` to find the limit of $u_{n+1} = u_n / 3 + 2$ with $u_0 = 10$, and give the first $n$ with $|u_n - 3| < 10^{-3}$.
2. (A) Prove `arithGeom_eq_add_sum` by induction on $n$, and deduce `arithGeom_zero_eq_sum`.
3. (B) Use the integral comparison for $f(x) = 1/x$ to show $\log(n + 1) \le H_n \le 1 + \log n$, where $H_n = \sum_{k=1}^n 1/k$.
4. (B) Show that $u_n = \log \binom{2n}{n}$ is superadditive, that is, $-u$ is subadditive, and find the limit of $u_n / n$.
5. (B) Show that $\sum_{n \ge 2} 1/(n \log n)$ diverges and $\sum_{n \ge 2} 1/(n (\log n)^2)$ converges, with the integral test.
6. (C) Let $u_n \ge 0$ be submultiplicative. Show that $\lim u_n^{1/n} = \inf_{n \ge 1} u_n^{1/n}$ by applying Fekete's lemma to $\log u_n$, and treat the case where some $u_n$ is $0$.

### Reference

<?reference?>
