---
title: Bernoulli numbers and polynomials
kind: api
modules:
  - Mathlib.NumberTheory.Bernoulli
  - Mathlib.NumberTheory.BernoulliPolynomials
explains:
  E2: [bernoulli, "bernoulli'", bernoulli'_eq_bernoulli, bernoulliPowerSeries_mul_exp_sub_one, sum_range_pow, bernoulli_eq_zero_of_odd, Bernoulli.vonStaudt_clausen, Polynomial.bernoulli, Polynomial.bernoulli_generating_function, Polynomial.sum_range_pow_eq_bernoulli_sub]
  E1: auto
families: []
requires: [V06, V02.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bernoulli numbers and polynomials

### Overview

The Bernoulli numbers $B_n$ are the rational numbers in the expansion
$$\frac{t}{e^t - 1} = \sum_{n \geq 0} B_n \frac{t^n}{n!}.$$
They give the closed formulas for the sums of powers $1^p + 2^p + \cdots + n^p$, the values of the Riemann zeta function at the even positive integers and at the negative integers, and the constant terms of Eisenstein series. The Bernoulli polynomials $B_n(x)$ extend them, with $B_n(0) = B_n$, and they are the values of the Hurwitz zeta function at the negative integers.

The module `Mathlib.NumberTheory.Bernoulli` defines the numbers with two sign conventions, proves the recursion, the generating function, Faulhaber's formula for sums of powers, the vanishing at odd indices, and the theorem of von Staudt and Clausen on the denominators. The module `Mathlib.NumberTheory.BernoulliPolynomials` defines the polynomials over `ℚ` and proves their basic identities. Section 4 uses both modules for the special values of zeta functions. The power series come from Volume 6.

### The library around it

#### Two conventions

There are two conventions for $B_1$. The library has both.

| Lean name | Recursion | $B_1$ | generating function |
|---|---|---|---|
| `bernoulli'` | $B'_n = 1 - \sum_{k < n}\binom{n}{k}\frac{B'_k}{n - k + 1}$ | $1/2$ | $\frac{te^t}{e^t - 1}$ |
| `bernoulli` | $B_n = (-1)^n B'_n$ | $-1/2$ | $\frac{t}{e^t - 1}$ |

The recursion of the first line is `bernoulli'_def`, and the definition of the second line is `bernoulli'_eq_bernoulli`. The two conventions differ only at $n = 1$, by `bernoulli_eq_bernoulli'_of_ne_one`, since $B'_n = 0$ for odd $n > 1$. The first values are `bernoulli_zero`, `bernoulli_one`, `bernoulli_two`, `bernoulli_three`, `bernoulli_four`, `bernoulli_five` and `bernoulli_six`, with $B_0 = 1$, $B_1 = -1/2$, $B_2 = 1/6$, $B_3 = 0$, $B_4 = -1/30$, $B_5 = 0$ and $B_6 = 1/42$. The primed versions are `bernoulli'_one`, `bernoulli'_two` and so on.

The recursions in the form of binomial sums are:

1. `sum_bernoulli'`: $\sum_{k < n}\binom{n}{k}B'_k = n$.
2. `sum_bernoulli`: $\sum_{k < n}\binom{n}{k}B_k = [n = 1]$.
3. `bernoulli_spec'`: the antidiagonal form, $\sum_{i + j = n}\binom{i + j}{j}\frac{B_i}{j + 1} = [n = 0]$.

#### Generating functions

Let $A$ be a commutative $\mathbb{Q}$-algebra. The power series `bernoulliPowerSeries A` is $\sum_n B_n t^n/n!$ in `PowerSeries A`, and `bernoulli'PowerSeries A` is the version with $B'_n$.

**Theorem.** In `PowerSeries A`,
$$\Big(\sum_n B_n\frac{t^n}{n!}\Big)(e^t - 1) = t, \qquad \Big(\sum_n B'_n\frac{t^n}{n!}\Big)(e^t - 1) = te^t.$$

*Proof.* The coefficient of $t^{n+1}$ in the product is $\sum_{k \leq n}\frac{B_k}{k!(n + 1 - k)!}$. After multiplication by $(n + 1)!$ this is $\sum_{k \leq n}\binom{n + 1}{k}B_k$, which is $[n = 0]$ by `sum_bernoulli`. $\square$

The statements are `bernoulliPowerSeries_mul_exp_sub_one` and `bernoulli'PowerSeries_mul_exp_sub_one`. They are identities of formal power series, so they hold over each $\mathbb{Q}$-algebra and need no convergence. From the first identity, $\frac{t}{e^t - 1} + \frac{t}{2}$ is an even function of $t$, so $B_n = 0$ for odd $n > 1$. This is `bernoulli_eq_zero_of_odd`, and `bernoulli'_eq_zero_of_odd` is the primed form.

#### Sums of powers

**Theorem (Faulhaber).** For $n, p \in \mathbb{N}$,
$$\sum_{k=0}^{n-1} k^p = \frac{1}{p + 1}\sum_{i=0}^{p}\binom{p + 1}{i}B_i\,n^{p + 1 - i}, \qquad \sum_{k=1}^{n} k^p = \frac{1}{p + 1}\sum_{i=0}^{p}\binom{p + 1}{i}B'_i\,n^{p + 1 - i}.$$

These are `sum_range_pow` and `sum_Ico_pow`. The proof multiplies the geometric series $\sum_{k < n}e^{kt} = \frac{e^{nt} - 1}{e^t - 1}$ by $t$ and compares coefficients with the generating function. The second formula follows from the first with $B'_1 = B_1 + 1$, which adds the term $n^p$. For $p = 1$ it gives $\sum_{k=1}^n k = \frac{1}{2}(n^2 + n)$, and for $p = 2$ it gives $\frac{1}{3}(n^3 + \frac{3}{2}n^2 + \frac{1}{2}n)$.

#### Denominators

**Theorem (von Staudt and Clausen).** For each $k$,
$$B_{2k} + \sum_{p\ \text{prime},\ (p - 1) \mid 2k}\frac{1}{p} \in \mathbb{Z}.$$

This is `Bernoulli.vonStaudt_clausen`. The sum runs over the primes below $2k + 2$, since $p - 1 \mid 2k$ with $k > 0$ forces $p \leq 2k + 1$. Some consequences for $k > 0$ and a prime $p$ with $p - 1 \mid 2k$:

| Lean name | Statement |
|---|---|
| `Bernoulli.padicValRat_bernoulli` | $v_p(B_{2k}) = -1$ |
| `Bernoulli.dvd_den_bernoulli` | $p$ divides the denominator of $B_{2k}$ |
| `Bernoulli.not_sq_dvd_den_bernoulli` | $p^2$ does not divide the denominator |
| `Bernoulli.not_dvd_num_bernoulli` | $p$ does not divide the numerator |
| `Bernoulli.padicValuation_bernoulli` | the same fact for the valuation `Rat.padicValuation p` |

So the denominator of $B_{2k}$ is the product of the primes $p$ with $p - 1 \mid 2k$. For example $B_{12} = -691/2730$, and $2730 = 2 \cdot 3 \cdot 5 \cdot 7 \cdot 13$ is the product of the primes $p$ with $p - 1 \mid 12$. The $p$-adic valuation is the one of Chapter 1.

#### Bernoulli polynomials

`Polynomial.bernoulli n` is the polynomial
$$B_n(X) = \sum_{i=0}^{n}\binom{n}{i}B_{n - i}X^i$$
in `Polynomial ℚ`, by `Polynomial.bernoulli_def` and `Polynomial.coeff_bernoulli`. The first ones are $B_0(X) = 1$ and $B_1(X) = X - \frac12$, which are `Polynomial.bernoulli_zero` and `Polynomial.bernoulli_one`. The values at $0$ and $1$ are the two conventions: $B_n(0) = B_n$ by `Polynomial.bernoulli_eval_zero`, and $B_n(1) = B'_n$ by `Polynomial.bernoulli_eval_one`.

| Lean name | Statement |
|---|---|
| `Polynomial.derivative_bernoulli` | $B_k'(X) = kB_{k-1}(X)$ |
| `Polynomial.bernoulli_eval_one_add` | $B_n(1 + x) = B_n(x) + nx^{n-1}$ |
| `Polynomial.bernoulli_eval_one_sub` | $B_n(1 - x) = (-1)^nB_n(x)$ |
| `Polynomial.bernoulli_eval_neg` | $B_n(-x) = (-1)^n(B_n(x) + nx^{n-1})$ |
| `Polynomial.sum_bernoulli` | $\sum_{k \leq n}\binom{n + 1}{k}B_k(X) = (n + 1)X^n$ |
| `Polynomial.sum_range_pow_eq_bernoulli_sub` | $(p + 1)\sum_{k < n}k^p = B_{p+1}(n) - B_{p+1}$ |

The polynomial versions of the composition identities are `Polynomial.bernoulli_comp_one_add_X`, `Polynomial.bernoulli_comp_one_sub_X` and `Polynomial.bernoulli_comp_neg_X`. The generating function holds with a parameter: for $t$ in a commutative $\mathbb{Q}$-algebra $A$,
$$\Big(\sum_n B_n(t)\frac{X^n}{n!}\Big)(e^X - 1) = Xe^{tX},$$
which is `Polynomial.bernoulli_generating_function`. Faulhaber's formula in the form of `Polynomial.sum_range_pow_eq_bernoulli_sub` follows from the second line of the table by a telescoping sum.

**Example.** $B_3(X) = X^3 - \frac32X^2 + \frac12X$, from the coefficients $B_0 = 1$, $3B_1 = -\frac32$ and $3B_2 = \frac12$. At $x = \frac14$ this gives $\frac{1}{64} - \frac{3}{32} + \frac18 = \frac{3}{64}$, which is `Polynomial.bernoulli_three_eval_one_quarter`. The symmetry $B_3(1 - x) = -B_3(x)$ gives $B_3(\frac34) = -\frac{3}{64}$ and $B_3(\frac12) = 0$. Values of this kind enter the special values of Dirichlet L-functions through the Hurwitz zeta function of Section 4.

#### Common errors

1. `bernoulli 1` is $-1/2$ and `bernoulli' 1` is $1/2$. A formula from a source with the other convention needs `bernoulli'_eq_bernoulli` or `bernoulli_eq_bernoulli'_of_ne_one` before it applies.
2. `Polynomial.bernoulli n` is a polynomial over `ℚ`. To evaluate it at a real or complex number, first map it with `Polynomial.map (algebraMap ℚ ℂ)` or use `Polynomial.aeval`.
3. `Bernoulli.vonStaudt_clausen` is a statement about the index $2k$. For $k = 0$ it says that $B_0 = 1$ is an integer, and for odd indices above $1$ the number is $0$ and the theorem says nothing.

### Exercises

1. (A) Compute $B_8$ from `sum_bernoulli` and the values up to $B_6$, and check the result against `Bernoulli.vonStaudt_clausen`.
2. (A) Use `sum_range_pow` to write $\sum_{k=0}^{n-1}k^3$ as a polynomial in $n$, and show that it is $\big(\frac{n(n - 1)}{2}\big)^2$.
3. (B) Show that $\frac{t}{e^t - 1} + \frac{t}{2}$ is an even power series, and deduce `bernoulli_eq_zero_of_odd` from `bernoulliPowerSeries_mul_exp_sub_one`.
4. (B) Prove `Polynomial.bernoulli_eval_one_sub` from `Polynomial.bernoulli_generating_function` by the substitution $t \mapsto 1 - t$, $X \mapsto -X$.
5. (C) Use `Polynomial.bernoulli_eval_one_add` and induction on $n$ to prove `Polynomial.sum_range_pow_eq_bernoulli_sub`.

### Reference

<?reference?>
