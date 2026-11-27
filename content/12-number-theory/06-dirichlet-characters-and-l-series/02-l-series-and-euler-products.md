---
title: L-series and Euler products
kind: theory
modules:
  - Mathlib.NumberTheory.LSeries.Basic
  - Mathlib.NumberTheory.LSeries.Convergence
  - Mathlib.NumberTheory.EulerProduct.Basic
  - Mathlib.NumberTheory.EulerProduct.DirichletLSeries
  - Mathlib.NumberTheory.LSeries.Dirichlet
  - Mathlib.NumberTheory.LSeries.Nonvanishing
explains:
  E3: [LSeries, EulerProduct.eulerProduct_completely_multiplicative_tprod, DirichletCharacter.LSeries_eulerProduct_tprod, DirichletCharacter.LFunction_ne_zero_of_one_le_re]
  E2: [LSeries.term, LSeriesSummable, LSeries.abscissaOfAbsConv, LSeries.abscissaOfAbsConv_le_of_le_const, LSeries_convolution', EulerProduct.eulerProduct_tprod, riemannZeta_eulerProduct_tprod, DirichletCharacter.LSeriesSummable_iff, DirichletCharacter.LSeries_ne_zero_of_one_lt_re, DirichletCharacter.LSeries.mul_mu_eq_one, ArithmeticFunction.LSeries_zeta_eq_riemannZeta, DirichletCharacter.LFunction, DirichletCharacter.LFunction_eq_LSeries, riemannZeta_ne_zero_of_one_le_re, DirichletCharacter.LFunction_apply_one_ne_zero, riemannZeta_residue_one]
  E1: auto
families: [LSeries.*, EulerProduct.*, DirichletCharacter.LSeries_*, DirichletCharacter.LFunction_*]
requires: [V12.C02, V15.C01, V15.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## L-series and Euler products

### Overview

The L-series of a function $f : \mathbb{N} \to \mathbb{C}$ is the series $L(f, s) = \sum_{n\ge1} f(n)n^{-s}$ in a complex variable $s$. For $f = 1$ it is the Riemann zeta function $\zeta(s)$, and for a Dirichlet character $\chi$ it is the Dirichlet L-series $L(\chi, s)$. An L-series turns Dirichlet convolution into a product, and, when $f$ is multiplicative, it is a product over the primes, the Euler product
$$\sum_{n\ge1}\frac{\chi(n)}{n^s} = \prod_p \frac{1}{1 - \chi(p)p^{-s}} \qquad (\operatorname{Re}s > 1).$$
The Euler product joins the analytic properties of $L(\chi, s)$ to the primes. Chapter 7 uses it in this way to prove Dirichlet's theorem and the prime number theorem.

The continuation of $L(\chi, s)$ and its nonvanishing on $\operatorname{Re}s = 1$ are stated as Mathlib has them.

### Definitions

**Definition (L-series).** For $f : \mathbb{N} \to \mathbb{C}$ and $s \in \mathbb{C}$, the $n$-th term is $f(n)n^{-s}$ for $n \ge 1$ and $0$ for $n = 0$. The L-series $L(f, s)$ is the sum of the terms when the series converges absolutely, and $0$ otherwise. The abscissa of absolute convergence $\sigma_a(f) \in [-\infty, \infty]$ is the infimum of the real $x$ at which the series converges absolutely.

Remarks. The power is $n^{-s} = e^{-s\log n}$, and $|n^{-s}| = n^{-\operatorname{Re}s}$. So the absolute convergence at $s$ depends only on $\operatorname{Re}s$, and the series converges absolutely for $\operatorname{Re}s > \sigma_a(f)$ and does not for $\operatorname{Re}s < \sigma_a(f)$. The value $f(0)$ plays no role.

::: mathlib
`LSeries` · `Mathlib.NumberTheory.LSeries.Basic`

`LSeries f s = ∑' n, LSeries.term f s n`, with `LSeries.term f s n = if n = 0 then 0 else f n / n ^ s`. The sum `∑'` is the unconditional sum, which is `0` for a series that is not summable. Summability is the predicate `LSeriesSummable f s`, and `LSeries.abscissaOfAbsConv f : EReal` is the abscissa. The notation `L f s` is available with `open LSeries`.

<?decl LSeries?>
:::

**Definition (Zeta and Dirichlet L-series).** $\zeta(s) = L(1, s) = \sum_{n\ge1}n^{-s}$ and $L(\chi, s) = \sum_{n\ge1}\chi(n)n^{-s}$ for a Dirichlet character $\chi$ modulo $N$, both for $\operatorname{Re}s > 1$.

::: mathlib
`DirichletCharacter.LFunction` · `Mathlib.NumberTheory.LSeries.DirichletContinuation`

`riemannZeta : ℂ → ℂ` and `DirichletCharacter.LFunction χ : ℂ → ℂ` are defined on all of `ℂ`, through Hurwitz zeta functions and their analytic continuation. They agree with the L-series for `1 < s.re`: `ArithmeticFunction.LSeries_zeta_eq_riemannZeta` and `DirichletCharacter.LFunction_eq_LSeries`. At $s = 1$ the value of `riemannZeta` is a convention, since there is a pole.

<?decl DirichletCharacter.LFunction?>
:::

### Theorems and proofs

**Theorem (Convergence).** If $|f(n)| \le C$ for all $n \ge 1$, then $L(f, s)$ converges absolutely for $\operatorname{Re}s > 1$, so $\sigma_a(f) \le 1$. In particular $\zeta(s)$ and $L(\chi, s)$ converge absolutely for $\operatorname{Re}s > 1$.

*Proof.* $|f(n)n^{-s}| \le Cn^{-\operatorname{Re}s}$, and $\sum n^{-x}$ converges for real $x > 1$ (Volume 15, Chapter 1). The values of a Dirichlet character have $|\chi(n)| \le 1$. $\square$

For a Dirichlet character the bound is sharp: since $\chi(m) = 1$ for $m \equiv 1 \pmod N$, the series $\sum|\chi(n)|n^{-x}$ contains $\sum_k (1 + kN)^{-x}$, which diverges for $x \le 1$.

::: mathlib
`DirichletCharacter.LSeriesSummable_iff` · `Mathlib.NumberTheory.LSeries.Dirichlet`

For `N ≠ 0`: `LSeriesSummable (fun n ↦ χ n) s ↔ 1 < s.re`. The general bound is `LSeries.abscissaOfAbsConv_le_of_le_const`: `(∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C) → abscissaOfAbsConv f ≤ 1`.

<?decl DirichletCharacter.LSeriesSummable_iff?>
:::

**Theorem (Product of L-series).** If $L(f, s)$ and $L(g, s)$ converge absolutely, then so does $L(f * g, s)$, where $(f * g)(n) = \sum_{de = n} f(d)g(e)$ is the Dirichlet convolution of Chapter 2, and $L(f * g, s) = L(f, s)L(g, s)$.

*Proof.* The double series $\sum_{d, e \ge 1} f(d)d^{-s}g(e)e^{-s}$ converges absolutely, with sum $L(f, s)L(g, s)$, as a product of two absolutely convergent series. Its terms are $f(d)g(e)(de)^{-s}$. An absolutely convergent double series may be summed in any grouping (Volume 15, Chapter 1). Group the terms by $n = de$: the group of $n$ is $(f * g)(n)n^{-s}$, and $\sum_n |(f*g)(n)n^{-s}|$ is at most the sum of the absolute values of the double series. $\square$

::: mathlib
`LSeries_convolution'` · `Mathlib.NumberTheory.LSeries.Convolution`

`LSeriesSummable f s → LSeriesSummable g s → LSeries (LSeries.convolution f g) s = LSeries f s * LSeries g s`. Here `LSeries.convolution` is the Dirichlet convolution of functions `ℕ → R`, written `f ⍟ g`, which agrees with the product of `ArithmeticFunction` on `ℕ+`. The version with abscissas is `LSeries_convolution`.

<?decl LSeries_convolution'?>
:::

**Theorem (Euler product).** Let $f : \mathbb{N} \to \mathbb{C}$ be completely multiplicative, $f(mn) = f(m)f(n)$ for all $m, n$ and $f(1) = 1$, with $\sum_n |f(n)| < \infty$ and $f(0) = 0$. Then $|f(p)| < 1$ for each prime $p$, and
$$\prod_p \frac{1}{1 - f(p)} = \sum_{n \ge 1}f(n),$$
where the product over the primes converges.

*Proof.* Since $\sum_k |f(p^k)| = \sum_k |f(p)|^k$ converges, $|f(p)| < 1$, and the geometric series gives $\frac{1}{1 - f(p)} = \sum_{k\ge0} f(p^k)$.

Let $P_N = \prod_{p \le N}\frac{1}{1 - f(p)}$. This is a finite product of absolutely convergent series, so it is the sum of all the products $f(p_1^{k_1})\cdots f(p_r^{k_r}) = f(p_1^{k_1}\cdots p_r^{k_r})$, where $p_1 < \cdots < p_r$ are the primes up to $N$. By unique factorization (Volume 2, Chapter 2), each $n \ge 1$ whose prime factors are all at most $N$ occurs exactly once. So $P_N = \sum_{n \in S_N} f(n)$, where $S_N$ is the set of these $n$. Each $n \le N$ lies in $S_N$, so
$$\Big|\sum_{n\ge1}f(n) - P_N\Big| \le \sum_{n > N}|f(n)| \to 0 \quad (N \to \infty). \qquad \square$$

**Corollary.** For $\operatorname{Re}s > 1$,
$$\zeta(s) = \prod_p \frac{1}{1 - p^{-s}}, \qquad L(\chi, s) = \prod_p \frac{1}{1 - \chi(p)p^{-s}}.$$

*Proof.* Apply the theorem to $f(n) = \chi(n)n^{-s}$, which is completely multiplicative since $\chi$ is and $(mn)^{-s} = m^{-s}n^{-s}$ for positive integers. The trivial character modulo $1$ gives $\zeta$. $\square$

::: mathlib
`EulerProduct.eulerProduct_completely_multiplicative_tprod` · `Mathlib.NumberTheory.EulerProduct.Basic`

For `f : ℕ →*₀ F` into a complete normed field with `Summable (‖f ·‖)`: `∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n`. A homomorphism `ℕ →*₀ F` is completely multiplicative and has `f 0 = 0` and `f 1 = 1` by definition. The version for multiplicative functions, with local factors `∑' e, f (p ^ e)`, is `EulerProduct.eulerProduct_tprod`. The proof follows the one above, with the sets `Nat.smoothNumbers N`.

<?decl EulerProduct.eulerProduct_completely_multiplicative_tprod?>
:::

::: mathlib
`DirichletCharacter.LSeries_eulerProduct_tprod` · `Mathlib.NumberTheory.EulerProduct.DirichletLSeries`

For `1 < s.re`: `∏' p : Nat.Primes, (1 - χ p * p ^ (-s))⁻¹ = LSeries (fun n ↦ χ n) s`. The case of zeta is `riemannZeta_eulerProduct_tprod`. The file also has the versions with limits of finite products and with `HasProd`.

<?decl DirichletCharacter.LSeries_eulerProduct_tprod?>
:::

**Theorem (No zeros for $\operatorname{Re}s > 1$).** $L(\chi, s) \ne 0$ for $\operatorname{Re}s > 1$.

*Proof.* Let $g(n) = \mu(n)\chi(n)$, with the Möbius function $\mu$ of Chapter 2. Then
$$(\chi * g)(n) = \sum_{de = n}\chi(d)\mu(e)\chi(e) = \chi(n)\sum_{e \mid n}\mu(e),$$
by complete multiplicativity, and $\sum_{e\mid n}\mu(e)$ is $1$ for $n = 1$ and $0$ otherwise (Chapter 2). So $\chi * g = \delta$, the unit of convolution. Both series converge absolutely for $\operatorname{Re}s > 1$, since $|g| \le 1$. The product theorem gives $L(\chi, s)L(g, s) = L(\delta, s) = 1$. $\square$

::: mathlib
`DirichletCharacter.LSeries_ne_zero_of_one_lt_re` · `Mathlib.NumberTheory.LSeries.Dirichlet`

The theorem, with the identity of the proof as `DirichletCharacter.LSeries.mul_mu_eq_one`: `LSeries χ s * LSeries (χ * μ) s = 1` for `1 < s.re`.

<?decl DirichletCharacter.LSeries_ne_zero_of_one_lt_re?>
:::

**Theorem (Nonvanishing on the line $\operatorname{Re}s = 1$).** Assume the following two facts, which this volume uses without proof: $\zeta$ extends to a holomorphic function on $\mathbb{C} \setminus \{1\}$ with $(s - 1)\zeta(s) \to 1$ as $s \to 1$, and $\zeta$ is holomorphic near each point $1 + it$ with $t \ne 0$. Then $\zeta(1 + it) \ne 0$ for real $t \ne 0$.

*Proof.* For $\sigma > 1$, the Euler product and the series $-\log(1 - z) = \sum_{k\ge1}z^k/k$ give $\log|\zeta(\sigma + it)| = \operatorname{Re}\sum_p\sum_{k}\frac{p^{-k\sigma}p^{-ikt}}{k} = \sum_{p,k}\frac{p^{-k\sigma}}{k}\cos(kt\log p)$. Since $3 + 4\cos\theta + \cos 2\theta = 2(1 + \cos\theta)^2 \ge 0$,
$$3\log|\zeta(\sigma)| + 4\log|\zeta(\sigma + it)| + \log|\zeta(\sigma + 2it)| = \sum_{p,k}\frac{p^{-k\sigma}}{k}\big(3 + 4\cos\theta_{p,k} + \cos 2\theta_{p,k}\big) \ge 0,$$
with $\theta_{p,k} = kt\log p$. So $|\zeta(\sigma)|^3|\zeta(\sigma + it)|^4|\zeta(\sigma + 2it)| \ge 1$ for $\sigma > 1$.

Suppose $\zeta(1 + it) = 0$. Since $\zeta$ is holomorphic near $1 + it$, $|\zeta(\sigma + it)| \le C(\sigma - 1)$ for $\sigma$ near $1$. By the first fact, $|\zeta(\sigma)| \le 2(\sigma - 1)^{-1}$ near $1$. Also $|\zeta(\sigma + 2it)| \le B$ for a constant $B$ and $\sigma$ near $1$, by the second fact for the point $1 + 2it$. Then the product is at most $8C^4B(\sigma - 1)$, which tends to $0$ as $\sigma \to 1^+$. This contradicts the bound $\ge 1$. $\square$

The same argument with $\chi^0, \chi, \chi^2$ in place of $\zeta(\sigma), \zeta(\sigma + it), \zeta(\sigma + 2it)$ proves $L(\chi, 1 + it) \ne 0$ when $\chi^2 \ne 1$ or $t \ne 0$. The remaining case, $L(\chi, 1) \ne 0$ for a real character $\chi \ne 1$, needs a different argument; it is the heart of Dirichlet's theorem.

::: mathlib
`DirichletCharacter.LFunction_ne_zero_of_one_le_re` · `Mathlib.NumberTheory.LSeries.Nonvanishing`

The statement for all Dirichlet characters: `χ ≠ 1 ∨ s ≠ 1 → 1 ≤ s.re → LFunction χ s ≠ 0`. It contains the case of zeta, `riemannZeta_ne_zero_of_one_le_re`, and the value at $1$, `DirichletCharacter.LFunction_apply_one_ne_zero`. The residue of zeta is `riemannZeta_residue_one`. The continuation that the theorem above assumes is part of the definitions of `riemannZeta` and `DirichletCharacter.LFunction`.

<?decl DirichletCharacter.LFunction_ne_zero_of_one_le_re?>
:::

### Examples

**Example ($\zeta(2)$).** $\zeta(2) = \sum 1/n^2 = \pi^2/6$, a theorem of Euler that Mathlib has as `riemannZeta_two`. The Euler product gives
$$\prod_p\frac{1}{1 - p^{-2}} = \frac{\pi^2}{6}, \qquad \prod_p\left(1 - \frac1{p^2}\right) = \frac{6}{\pi^2}.$$
The right side is the density of the pairs of integers with $\gcd = 1$: the probability that $p$ divides both is $1/p^2$, and these events are independent for different primes.

**Example ($L(\chi_{-4}, s)$).** For the character $\chi_{-4}$ modulo $4$ of Section 1,
$$L(\chi_{-4}, s) = 1 - \frac1{3^s} + \frac1{5^s} - \frac1{7^s} + \cdots = \prod_{p \equiv 1 (4)}\frac{1}{1 - p^{-s}}\prod_{p \equiv 3 (4)}\frac{1}{1 + p^{-s}}.$$
At $s = 1$ the series converges conditionally to $\pi/4$ by the series of Leibniz. Exercise 6 links this L-series to the sums of two squares of Chapter 4.

**Counterexample (The Euler product at $s = 1$).** The product $\prod_p(1 - 1/p)^{-1}$ diverges to $\infty$, since its partial products are at least $\sum_{n \le N}1/n$, by the argument of the proof. So the theorem fails at $s = 1$; Chapter 7 uses this divergence to prove that $\sum 1/p$ diverges.

**Counterexample (A function that is not multiplicative).** For $f(n) = 1$ if $n = 2$ and $0$ otherwise, $L(f, s) = 2^{-s}$ has no Euler product of the form of the theorem: the product $\prod_p\sum_k f(p^k)$ is $0$, since the factor at $p = 3$ is $f(1) = 0$.

### The library around it

The folder `Mathlib.NumberTheory.LSeries` has the general theory, with holomorphy in `Deriv` and uniqueness of coefficients in `Injectivity`. The functions on all of `ℂ` come from `HurwitzZeta`, `RiemannZeta` and `DirichletContinuation`, with the functional equations. `Mathlib.NumberTheory.LSeries.Nonvanishing` proves the nonvanishing on $\operatorname{Re}s \ge 1$ for all characters. The file `Mathlib.NumberTheory.EulerProduct.Basic` gives Euler products in general.

Common errors of a learner:

- `LSeries f s` is `0`, not undefined, when the series does not converge absolutely. A statement about `LSeries` usually needs `LSeriesSummable f s` or `1 < s.re`.
- `riemannZeta s` and `LSeries 1 s` agree only for `1 < s.re`. For other `s`, use `riemannZeta`.

### Exercises

1. (A) Show that $\zeta(s)^2 = \sum_n d(n)n^{-s}$ for $\operatorname{Re}s > 1$, with $d(n)$ the number of divisors.
2. (A) Show that $1/\zeta(s) = \sum\mu(n)n^{-s}$ and $\zeta(s - 1)/\zeta(s) = \sum\varphi(n)n^{-s}$ for $\operatorname{Re}s > 2$.
3. (B) Show that $\sigma_a(\mu) = 1$. Hint: $|\mu(p)| = 1$ for each prime, and $\sum 1/p$ diverges (Chapter 7).
4. (B) Show that $\sum_n\lambda(n)n^{-s} = \zeta(2s)/\zeta(s)$ for $\operatorname{Re}s > 1$, with Liouville's function $\lambda(n) = (-1)^{\Omega(n)}$.
5. (B) Show that $-\zeta'(s)/\zeta(s) = \sum_n\Lambda(n)n^{-s}$ for $\operatorname{Re}s > 1$, with the von Mangoldt function $\Lambda$ of Chapter 2.
6. (B) Let $r(n)$ be the number of pairs $(x, y) \in \mathbb{Z}^2$ with $x^2 + y^2 = n$. Show that $\sum_{n\ge1} r(n)n^{-s} = 4\zeta(s)L(\chi_{-4}, s)$, from Jacobi's formula $r(n) = 4\sum_{d \mid n}\chi_{-4}(d)$, which this volume does not prove.
7. (C) Let $\chi$ be a real nontrivial character. Show that $F(s) = \zeta(s)L(\chi, s)$ has an Euler product whose local factors have nonnegative coefficients, and that the coefficient of $n^{-s}$ is at least $1$ when $n$ is a square. Deduce that $\sum_n a_n n^{-1/2}$ diverges, where $F(s) = \sum a_n n^{-s}$.

### Notes and history

Euler found the product formula for $\zeta(s)$ in 1737, and with it a new proof that there are infinitely many primes. Dirichlet introduced the L-series of characters in 1837. Riemann studied $\zeta(s)$ as a function of a complex variable in 1859 and proved the continuation and the functional equation. The inequality $3 + 4\cos\theta + \cos2\theta \ge 0$ is due to Mertens. A reference is Apostol, *Introduction to Analytic Number Theory*, Chapters 11 and 12.

### Reference

<?reference?>
