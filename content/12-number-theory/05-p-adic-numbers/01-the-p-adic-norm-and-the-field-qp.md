---
title: The p-adic norm and the field Q_p
kind: theory
modules:
  - Mathlib.NumberTheory.Padics.PadicNorm
  - Mathlib.NumberTheory.Padics.PadicNumbers
  - Mathlib.NumberTheory.Ostrowski
explains:
  E3: [padicNorm, padicNorm.nonarchimedean, Padic, Rat.AbsoluteValue.equiv_real_or_padic]
  E2: [padicNorm.mul, padicNorm.add_eq_max_of_ne, padicNorm.dvd_iff_norm_le, padicNorm.values_discrete, padicNorm.padicNorm_p_of_prime, padicNorm.int_lt_one_iff, padicNormE, PadicSeq, PadicSeq.stationary, Padic.complete, Padic.rat_dense, Padic.valuation, Padic.norm_eq_zpow_neg_valuation, Padic.add_eq_max_of_ne, Rat.AbsoluteValue.padic, Rat.AbsoluteValue.real, Rat.AbsoluteValue.equiv_real_of_unbounded, Rat.AbsoluteValue.equiv_padic_of_bounded]
  E1: auto
families: [padicNorm.*, Padic.*, PadicSeq.*, Rat.AbsoluteValue.*]
requires: [V12.C01, V13.C03, V15.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The p-adic norm and the field Q_p

### Overview

The real numbers are the completion of $\mathbb{Q}$ for the usual absolute value. For each prime $p$ there is a second absolute value on $\mathbb{Q}$, the $p$-adic norm, for which a number is small when it is divisible by a high power of $p$. Its completion is the field $\mathbb{Q}_p$ of $p$-adic numbers. Ostrowski's theorem says that, up to a power, these are all the absolute values on $\mathbb{Q}$: the usual one and one for each prime.

The completion uses Cauchy sequences, as in Volume 13, Chapter 3. The norm of $\mathbb{Q}_p$ satisfies the strong triangle inequality $|x + y| \le \max(|x|, |y|)$, and this inequality makes the analysis of $\mathbb{Q}_p$ very different from that of $\mathbb{R}$: a series converges if and only if its terms tend to $0$.

### Definitions

**Definition (Absolute value).** An absolute value on a field $K$ is a function $f : K \to \mathbb{R}$ such that $f(x) \ge 0$, $f(x) = 0$ if and only if $x = 0$, $f(xy) = f(x)f(y)$, and $f(x + y) \le f(x) + f(y)$. It is nonarchimedean if $f(x + y) \le \max(f(x), f(y))$ for all $x, y$. It is trivial if $f(x) = 1$ for all $x \ne 0$. Two absolute values $f$ and $g$ are equivalent if $g = f^c$ for a real $c > 0$.

**Definition ($p$-adic norm).** Let $p$ be a prime. For a nonzero rational $q$, let $v_p(q) \in \mathbb{Z}$ be its $p$-adic valuation (Chapter 1): $q = p^{v_p(q)} \frac ab$ with $a, b$ integers prime to $p$. The $p$-adic norm is
$$|q|_p = p^{-v_p(q)} \quad (q \ne 0), \qquad |0|_p = 0.$$

Remarks. So $|q|_p \le 1$ if and only if $p$ does not divide the denominator of $q$ in lowest terms, and $|n|_p \le p^{-k}$ for an integer $n$ if and only if $p^k \mid n$. The values of the norm are the powers $p^k$, $k \in \mathbb{Z}$, and $0$.

::: mathlib
`padicNorm` · `Mathlib.NumberTheory.Padics.PadicNorm`

`padicNorm p : ℚ → ℚ` takes rational values, so that computations stay in `ℚ`. It is defined for each natural number `p`, and most lemmas need `[Fact p.Prime]`. The absolute value with real values is `Rat.AbsoluteValue.padic p`, in `Mathlib.NumberTheory.Ostrowski`, and `Rat.AbsoluteValue.padic_eq_padicNorm` links the two.

<?decl padicNorm?>
:::

**Definition ($\mathbb{Q}_p$).** A sequence $(a_n)$ in $\mathbb{Q}$ is Cauchy for $|\cdot|_p$ if for each $\varepsilon > 0$ there is $N$ with $|a_n - a_m|_p < \varepsilon$ for $n, m \ge N$. It is null if $|a_n|_p \to 0$. The field $\mathbb{Q}_p$ is the quotient of the ring of Cauchy sequences by the ideal of null sequences. A rational $q$ maps to the class of the constant sequence.

::: mathlib
`Padic` · `Mathlib.NumberTheory.Padics.PadicNumbers`

`Padic p`, with the notation `ℚ_[p]`, is the general completion `CauSeq.Completion.Cauchy (padicNorm p)`. The type of the Cauchy sequences is `PadicSeq p`. The norm is first `padicNormE`, with values in `ℚ`, and then the real norm `‖x‖` of a normed field.

<?decl Padic?>
:::

### Theorems and proofs

**Theorem (Properties of the $p$-adic norm).** For $q, r \in \mathbb{Q}$:

1. $|qr|_p = |q|_p|r|_p$;
2. $|q + r|_p \le \max(|q|_p, |r|_p)$;
3. if $|q|_p \ne |r|_p$, then $|q + r|_p = \max(|q|_p, |r|_p)$.

*Proof.* If $q$ or $r$ is $0$, each statement is clear. Let $q, r \ne 0$.

(1) Chapter 1 proves $v_p(qr) = v_p(q) + v_p(r)$, and $p^{-(a + b)} = p^{-a}p^{-b}$.

(2) Write $q = p^a\frac{u}{w}$ and $r = p^b\frac{u'}{w'}$ with $u, w, u', w'$ prime to $p$, and let $a \le b$. Then
$$q + r = p^a\,\frac{uw' + p^{b - a}u'w}{ww'}.$$
The denominator $ww'$ is prime to $p$. So if $q + r \ne 0$, then $v_p(q + r) \ge a = \min(v_p(q), v_p(r))$, which is statement (2).

(3) Let $|q|_p < |r|_p$. By (2), $|q + r|_p \le |r|_p$. Also $r = (q + r) - q$, and $|{-q}|_p = |q|_p$, so $|r|_p \le \max(|q + r|_p, |q|_p)$. The maximum is not $|q|_p$, since $|q|_p < |r|_p$. So $|r|_p \le |q + r|_p$. $\square$

::: mathlib
`padicNorm.nonarchimedean` · `Mathlib.NumberTheory.Padics.PadicNorm`

The strong triangle inequality, `padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r)`. The other statements are `padicNorm.mul` and `padicNorm.add_eq_max_of_ne`. The link with divisibility is `padicNorm.dvd_iff_norm_le`: `↑(p ^ n) ∣ z ↔ padicNorm p z ≤ p ^ (-n)`.

<?decl padicNorm.nonarchimedean?>
:::

**Theorem (Ostrowski).** Every nontrivial absolute value on $\mathbb{Q}$ is equivalent to the usual absolute value $|\cdot|$ or to $|\cdot|_p$ for exactly one prime $p$.

*Proof.* Let $f$ be a nontrivial absolute value. Then $f(1)^2 = f(1)$ gives $f(1) = 1$, and $f(-1)^2 = 1$ gives $f(-1) = 1$. So $f(-x) = f(x)$, and $f$ is fixed by its values on the positive integers, by multiplicativity.

Case 1: $f(n) > 1$ for some positive integer $n$. Let $m, n \ge 2$ be integers. Write $n$ in base $m$: $n = \sum_{i=0}^{k} c_i m^i$ with $0 \le c_i < m$ and $m^k \le n$, so $k \le \log n/\log m$. Each $f(c_i) \le c_i \le m$ by the triangle inequality applied to $1 + \cdots + 1$. With $M = \max(1, f(m))$,
$$f(n) \le \sum_{i=0}^k f(c_i)f(m)^i \le (k + 1)\,m\,M^{k} \le \left(\frac{\log n}{\log m} + 1\right) m\, M^{\log n/\log m}.$$
Apply this to $n^r$ in place of $n$ and take $r$-th roots:
$$f(n) \le \left(\frac{r\log n}{\log m} + 1\right)^{1/r} m^{1/r}\, M^{\log n/\log m}.$$
As $r \to \infty$, the first two factors tend to $1$. So $f(n) \le \max(1, f(m))^{\log n/\log m}$ for all $m, n \ge 2$. Take $n$ with $f(n) > 1$: then $f(m) > 1$ for every $m \ge 2$, so the inequality reads $f(n)^{1/\log n} \le f(m)^{1/\log m}$. By symmetry the two sides are equal, so $f(m)^{1/\log m}$ is a constant $e^s$ with $s > 0$, and $f(m) = m^s$ for $m \ge 2$. So $f(x) = |x|^s$ for all $x \in \mathbb{Q}$.

Case 2: $f(n) \le 1$ for every integer $n$. First, $f$ is nonarchimedean on $\mathbb{Z}$. For integers $a, b$ and $r \ge 1$, the binomial theorem and $f(\binom ri) \le 1$ give
$$f(a + b)^r = f\Big(\sum_{i=0}^{r}\binom ri a^ib^{r-i}\Big) \le (r + 1)\max(f(a), f(b))^r.$$
Take $r$-th roots and let $r \to \infty$: $f(a + b) \le \max(f(a), f(b))$.

Let $I = \{n \in \mathbb{Z} : f(n) < 1\}$. Then $I$ is an ideal: it is closed under addition by the inequality above and under multiplication by integers since $f \le 1$ on $\mathbb{Z}$. It does not contain $1$. It is not $\{0\}$: since $f$ is nontrivial, $f(x) \ne 1$ for some $x = a/b$, so $f(a) \ne 1$ or $f(b) \ne 1$, and that value is less than $1$. It is prime: if $f(ab) = f(a)f(b) < 1$ with $f(a), f(b) \le 1$, then $f(a) < 1$ or $f(b) < 1$. So $I = p\mathbb{Z}$ for a prime $p$ (Volume 2, Chapter 2). Let $f(p) = p^{-t}$ with $t > 0$. Each integer $n \ne 0$ is $p^k m$ with $p \nmid m$, so $m \notin I$, $f(m) = 1$, and $f(n) = p^{-tk} = |n|_p^t$. So $f = |\cdot|_p^t$ on $\mathbb{Q}$.

Uniqueness. The cases exclude each other, since $|2| > 1$ while $|n|_p \le 1$ on $\mathbb{Z}$. For primes $p \ne q$, $|p|_p < 1 = |p|_q$, and a power of $|\cdot|_q$ gives $|p|_q^c = 1$, so $|\cdot|_p$ and $|\cdot|_q$ are not equivalent. $\square$

::: mathlib
`Rat.AbsoluteValue.equiv_real_or_padic` · `Mathlib.NumberTheory.Ostrowski`

The statement: for `f : AbsoluteValue ℚ ℝ` with `f.IsNontrivial`, `f ≈ Rat.AbsoluteValue.real ∨ ∃! p, ∃ (_ : Fact p.Prime), f ≈ Rat.AbsoluteValue.padic p`. The two cases of the proof are `Rat.AbsoluteValue.equiv_real_of_unbounded` and `Rat.AbsoluteValue.equiv_padic_of_bounded`. The relation `≈` is `AbsoluteValue.IsEquiv`, defined by order comparisons, which is equivalent to the definition by powers.

<?decl Rat.AbsoluteValue.equiv_real_or_padic?>
:::

**Lemma (Stationary norms).** Let $(a_n)$ be a Cauchy sequence in $\mathbb{Q}$ for $|\cdot|_p$ that is not null. Then $|a_n|_p$ is constant for $n$ large.

*Proof.* Since the sequence is not null, there is $\varepsilon > 0$ with $|a_m|_p \ge \varepsilon$ for infinitely many $m$. Choose $N$ with $|a_n - a_m|_p < \varepsilon$ for $n, m \ge N$, and fix $m \ge N$ with $|a_m|_p \ge \varepsilon$. For $n \ge N$, $|a_n - a_m|_p < |a_m|_p$, so by property (3) $|a_n|_p = |(a_n - a_m) + a_m|_p = |a_m|_p$. $\square$

**Theorem (The field $\mathbb{Q}_p$).** Put $|x|_p = \lim_n |a_n|_p$ for the class $x$ of $(a_n)$. This is a well defined nonarchimedean absolute value on $\mathbb{Q}_p$, its values are $0$ and the powers $p^k$ with $k \in \mathbb{Z}$, $\mathbb{Q}$ is dense in $\mathbb{Q}_p$, and $\mathbb{Q}_p$ is complete.

*Proof.* The limit exists: for a null sequence it is $0$, and otherwise the lemma gives an eventually constant sequence, whose value is a power of $p$. Two Cauchy sequences with null difference have the same limit, since $\big||a_n|_p - |b_n|_p\big| \le |a_n - b_n|_p$. Multiplicativity and the strong triangle inequality hold term by term and pass to the limit. Only null sequences have the limit $0$, so $|x|_p = 0$ only for $x = 0$.

$\mathbb{Q}_p$ is a field: if $(a_n)$ is not null, then $a_n \ne 0$ for $n \ge N$ by the lemma, and the sequence $(b_n)$ with $b_n = a_n^{-1}$ for $n \ge N$ and $b_n = 0$ otherwise is Cauchy, since $|a_n^{-1} - a_m^{-1}|_p = |a_m - a_n|_p/|a_n a_m|_p$ and the denominator is constant. Its class is the inverse.

Density: for $x$ the class of $(a_n)$ and $\varepsilon > 0$, take $N$ with $|a_n - a_m|_p < \varepsilon$ for $n, m \ge N$. Then $|x - a_N|_p = \lim_n |a_n - a_N|_p \le \varepsilon$.

Completeness: the construction is the completion of a metric space, and Volume 13, Chapter 3 proves that a completion is complete, with the density above as the key step. $\square$

The valuation extends: for $x \ne 0$ in $\mathbb{Q}_p$ there is a unique $v_p(x) \in \mathbb{Z}$ with $|x|_p = p^{-v_p(x)}$.

::: mathlib
`Padic.complete` · `Mathlib.NumberTheory.Padics.PadicNumbers`

The instance `Padic.complete` gives completeness for Cauchy sequences in the sense of `CauSeq`. The lemma of stationary norms is `PadicSeq.stationary`. Density of `ℚ` is `Padic.rat_dense`. The valuation is `Padic.valuation : ℚ_[p] → ℤ`, with `Padic.norm_eq_zpow_neg_valuation`.

<?decl Padic.complete?>
:::

**Corollary (Convergence of series).** In $\mathbb{Q}_p$, a series $\sum x_n$ converges if and only if $|x_n|_p \to 0$.

*Proof.* If the series converges, the terms tend to $0$, as in $\mathbb{R}$. Conversely, for the partial sums $s_n$ and $m > n$, the strong triangle inequality gives $|s_m - s_n|_p \le \max_{n < k \le m}|x_k|_p$, which is small for $n$ large. So $(s_n)$ is Cauchy and converges by completeness. $\square$

### Examples

**Example (Norms of rationals).** $600 = 2^3 \cdot 3 \cdot 5^2$, so $|600|_2 = \frac18$, $|600|_3 = \frac13$, $|600|_5 = \frac1{25}$, and $|600|_p = 1$ for the other primes. The product of all the norms with the usual absolute value is $\frac18 \cdot \frac13 \cdot \frac1{25} \cdot 600 = 1$. The same product formula $|q|\prod_p |q|_p = 1$ holds for each nonzero rational $q$, by the factorization of $q$. For $q = \frac{9}{14}$, $|q|_3 = \frac19$, $|q|_2 = 2$ and $|q|_7 = 7$.

**Example ($-1$ as a series).** In $\mathbb{Q}_p$, $|p^n|_p = p^{-n} \to 0$, so $\sum_{n \ge 0} p^n$ converges. Its partial sums are $\frac{1 - p^{n+1}}{1 - p}$, and $|p^{n+1}/(1 - p)|_p \to 0$, so the sum is $\frac{1}{1 - p}$. Multiply by $p - 1$:
$$-1 = \sum_{n \ge 0} (p - 1)p^n = (p - 1) + (p - 1)p + (p - 1)p^2 + \cdots.$$
For $p = 2$ it reads $-1 = 1 + 2 + 4 + \cdots$.

**Counterexample (The usual absolute value is archimedean).** $|1 + 1| = 2 > \max(|1|, |1|)$. More generally, a nonarchimedean absolute value has $f(n) \le 1$ for each integer $n$, by induction on $n$, so case 1 of Ostrowski's theorem is exactly the archimedean case.

### The library around it

Mathlib has three norms in this area: `padicNorm p` on `ℚ`, `padicNormE` on `ℚ_[p]` with rational values, and the real norm `‖x‖`. The completion `CauSeq.Completion` also builds `ℝ`, so `ℚ_[p]` and `ℝ` come from one construction. The valuation has the lemmas `Padic.valuation_mul` and `Padic.le_valuation_add`.

Common errors of a learner:

- `padicNorm p q` is a rational number. To compare it with a real `ε`, cast it, or use the real norm on `ℚ_[p]` and the cast `(q : ℚ_[p])`.
- The notation `ℚ_[p]` needs `[Fact p.Prime]` in context. Write `variable {p : ℕ} [Fact p.Prime]` once at the top of a file.

### Exercises

1. (A) Compute $|q|_2$, $|q|_3$ and $|q|_5$ for $q = \frac{360}{49}$ and $q = -\frac{1}{1000}$.
2. (A) Show that $|n!|_p = p^{-\sum_{k\ge1}\lfloor n/p^k\rfloor}$, with the formula of Legendre from Chapter 1, and compute $|100!|_5$.
3. (A) Show that $\lim_{n\to\infty} p^n = 0$ and that the sequence $(n)$ of positive integers has no limit in $\mathbb{Q}_p$.
4. (B) Show that in $\mathbb{Q}_p$ every open ball $B(a, r) = \{x : |x - a|_p < r\}$ is also closed, and that each point of the ball is a center: $B(b, r) = B(a, r)$ for $b \in B(a, r)$.
5. (B) Show that $\sum_{n\ge0} n!$ converges in $\mathbb{Q}_p$ for each prime $p$.
6. (B) Show that $\mathbb{Q}_p$ has no order compatible with the field structure. Hint: Section 2 shows that $1 - p$ is a square in $\mathbb{Q}_p$ for $p$ odd and that $-7$ is a square in $\mathbb{Q}_2$; in an ordered field a square is not negative.
7. (C) Prove the product formula $|q|\prod_p|q|_p = 1$ for $q \in \mathbb{Q}^\times$, and deduce that if $|q|_p \le 1$ for every prime $p$, then $q \in \mathbb{Z}$.

### Notes and history

Kurt Hensel introduced the $p$-adic numbers around 1897, by analogy with the expansion of functions in power series at a point. Alexander Ostrowski proved the classification of the absolute values on $\mathbb{Q}$ in 1916. A reference is Gouvêa, *p-adic Numbers: An Introduction*, Chapters 2 and 3, and Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter 1.

### Reference

<?reference?>
