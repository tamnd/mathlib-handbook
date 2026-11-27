---
title: The irrationality of e and pi
kind: theory
modules:
  - Mathlib.Analysis.Real.Pi.Irrational
  - Mathlib.Topology.Instances.Irrational
explains:
  E3: [irrational_pi]
  E2: [dense_irrational, eventually_residual_irrational]
  E1: [Irrational, irrational_iff_ne_rational, Real.sum_le_exp_of_nonneg, Real.exp_bound']
families: []
requires: [V02, V13, V15.C01, V15.C03, V15.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The irrationality of e and pi

### Overview

The two constants of analysis, $e$ and $\pi$, are irrational. Both proofs below follow one idea: assume the number is rational, build from it an expression that is an integer by the assumption and lies strictly between $0$ and $1$ by an estimate. For $e$ the expression is $(n-1)!$ times the tail of $\sum 1/m!$, with the series of Chapter 5. For $\pi$ it comes from Niven's polynomial (1947), with the derivatives of $\sin$ and $\cos$ and the mean value theorem of Chapter 3. Mathlib has `irrational_pi`, and at this commit no lemma for the irrationality of $e$. The section ends with the density of the irrationals.

### Definitions

**Definition (Irrational number).** A real number $x$ is irrational if $x \ne a/b$ for all integers $a, b$ with $b \ne 0$.

A positive rational number can be written $a/b$ with $a, b > 0$. The proofs below use this form.

::: mathlib
`Irrational` · `Mathlib.NumberTheory.Real.Irrational`

`Irrational x` is defined as `x ∉ Set.range ((↑) : ℚ → ℝ)`. The form with integers is the lemma `irrational_iff_ne_rational`. A proof of irrationality is a proof of a negation: it introduces a rational `q` with `(q : ℝ) = x` and derives `False`. The arithmetic theory belongs to Volume 12.

<?decl Irrational?>
:::

**Definition (Residual set).** A subset of $\mathbb{R}$ is residual if it contains a countable intersection of dense open sets.

By the Baire category theorem of Volume 13, a residual subset of $\mathbb{R}$ is dense. Its complement is called meagre.

### Theorems and proofs

**Lemma (Tails of the series for e).** Let $s_n = \sum_{m=0}^{n-1} 1/m!$ for $n \ge 1$. Then
$$\frac{1}{n!} \le e - s_n \le \frac{1}{n!} \cdot \frac{n+1}{n}.$$

*Proof.* By Chapter 5, $e = \sum_{m=0}^{\infty} 1/m!$, a series of positive terms. So $e - s_n = \sum_{m \ge n} 1/m!$. The first term is $1/n!$, which gives the lower bound. For $j \ge 0$,
$$\frac{n!}{(n+j)!} = \frac{1}{(n+1)(n+2)\cdots(n+j)} \le \frac{1}{(n+1)^j},$$
since each factor is at least $n+1$. Sum the geometric series:
$$e - s_n = \frac{1}{n!}\sum_{j \ge 0} \frac{n!}{(n+j)!} \le \frac{1}{n!}\sum_{j \ge 0} \frac{1}{(n+1)^j} = \frac{1}{n!} \cdot \frac{1}{1 - 1/(n+1)} = \frac{1}{n!} \cdot \frac{n+1}{n}. \quad \square$$

::: mathlib
`Real.exp_bound'` · `Mathlib.Analysis.Complex.Exponential`

For `0 ≤ x ≤ 1` and `0 < n`, `exp x ≤ ∑ m ∈ range n, x ^ m / m ! + x ^ n * (n + 1) / (n ! * n)`. With `x = 1` this is the upper bound of the lemma. The lower bound follows from `Real.sum_le_exp_of_nonneg`, the inequality `∑ i ∈ range n, x ^ i / i ! ≤ exp x` for `0 ≤ x`,, with `n + 1` terms. Both belong to Volume 19, and with them the next proof needs no new analysis in Lean.

<?decl Real.exp_bound'?>
:::

**Theorem (Irrationality of e).** The number $e$ is irrational.

*Proof.* Suppose $e = a/b$ with integers $a$ and $b \ge 1$. Choose an integer $n \ge 2$ with $n - 1 \ge b$, for example $n = b + 1$. Put
$$N = (n-1)!\,(e - s_n) = (n-1)!\,e - \sum_{m=0}^{n-1} \frac{(n-1)!}{m!}.$$
Each quotient $(n-1)!/m!$ with $m \le n - 1$ is an integer. Also $(n-1)!\,e = a \cdot (n-1)!/b$ is an integer, because $b \le n - 1$ divides $(n-1)!$. So $N$ is an integer. Multiply the bounds of the lemma by $(n-1)!$, and use $(n-1)!/n! = 1/n$:
$$0 < \frac{1}{n} \le N \le \frac{n+1}{n^2}.$$
For $n \ge 2$, $n^2 - n - 1 = n(n-1) - 1 \ge 1$, so $n + 1 < n^2$ and $N < 1$. An integer cannot lie strictly between $0$ and $1$. $\square$

Many books multiply by $n!$ instead. Then the upper bound $(n+1)/n$ is above $1$, and the argument needs one more step. The factor $(n-1)!$ avoids it.

**Theorem (Niven).** The number $\pi$ is irrational.

*Proof.* Suppose $\pi = a/b$ with positive integers $a$ and $b$. Fix $n \ge 1$, chosen at the end, and put
$$f(x) = \frac{x^n (a - bx)^n}{n!}.$$

Step 1: $f(\pi - x) = f(x)$. Since $b\pi = a$, $a - b(\pi - x) = bx$ and $b(\pi - x) = a - bx$. So $f(\pi - x) = (b(\pi - x))^n x^n / n! = f(x)$.

Step 2: every derivative $f^{(j)}(0)$ is an integer. Expand $x^n (a - bx)^n = \sum_{j=n}^{2n} c_j x^j$, with integers $c_j$. Then $f(x) = \frac{1}{n!}\sum_{j=n}^{2n} c_j x^j$, and $f^{(j)}(0) = j!\,c_j / n!$. This is $0$ for $j < n$ and for $j > 2n$, and an integer for $n \le j \le 2n$, because $n!$ divides $j!$.

Step 3: every derivative $f^{(j)}(\pi)$ is an integer. Differentiate Step 1 $j$ times: $(-1)^j f^{(j)}(\pi - x) = f^{(j)}(x)$, so $f^{(j)}(\pi) = (-1)^j f^{(j)}(0)$.

Step 4: an auxiliary function. Put
$$F = f - f'' + f^{(4)} - \cdots + (-1)^n f^{(2n)} = \sum_{k=0}^{n} (-1)^k f^{(2k)}.$$
By Steps 2 and 3, $F(0)$ and $F(\pi)$ are integers. In $F + F'' = \sum_k (-1)^k (f^{(2k)} + f^{(2k+2)})$ the terms cancel in pairs, leaving $f + (-1)^n f^{(2n+2)} = f$, since $f$ has degree $2n$.

Step 5: put $G(x) = F'(x)\sin x - F(x)\cos x$. By the product rule,
$$G'(x) = F''(x)\sin x + F'(x)\cos x - F'(x)\cos x + F(x)\sin x = (F'' + F)(x)\sin x = f(x)\sin x.$$
At the end points, $\sin 0 = \sin \pi = 0$, $\cos 0 = 1$ and $\cos \pi = -1$. So $G(\pi) - G(0) = F(\pi) + F(0)$, an integer.

Step 6: an estimate. By the mean value theorem there is $c \in (0, \pi)$ with
$$G(\pi) - G(0) = \pi\, G'(c) = \pi\, f(c) \sin c.$$
If $0 < x < \pi$, then $0 < a - bx < a$ and $0 < \sin x \le 1$. So
$$0 < G(\pi) - G(0) < \pi \cdot \frac{\pi^n a^n}{n!} = \pi \cdot \frac{(\pi a)^n}{n!}.$$
By Chapter 1, $q^n / n! \to 0$ for each real $q$. Choose $n$ with $\pi (\pi a)^n / n! < 1$. Then the integer $G(\pi) - G(0)$ lies strictly between $0$ and $1$. This is impossible. $\square$

The usual form of Step 6 is the integral $\int_0^\pi f(x)\sin x\,dx = F(\pi) + F(0)$. The mean value theorem replaces it here, because this volume has no integration.

::: mathlib
`irrational_pi` · `Mathlib.Analysis.Real.Pi.Irrational`

`Irrational π`, the only declaration of its module that the index shows. The index records the statement only, with no docstring, so this section does not describe the formal proof. A reader who wants the formal route should read the source file. For the use of the theorem the statement is enough: with the arithmetic API of `Irrational` it gives the irrationality of $\pi + q$, $q\pi$ and $\pi/q$ for every nonzero rational $q$.

<?decl irrational_pi?>
:::

**Theorem (Density).** The irrational numbers are dense in $\mathbb{R}$, and they form a residual set.

*Proof.* For density, let $u < v$. By the density of the rationals (Volume 2) there is a rational $r$ with $u - \sqrt2 < r < v - \sqrt2$. Then $r + \sqrt2 \in (u, v)$. It is irrational: if $r + \sqrt2 = q$ with $q$ rational, then $\sqrt2 = q - r$ is rational, which is false. For the residual property, the set of irrationals is $\bigcap_{r \in \mathbb{Q}} (\mathbb{R} \setminus \{r\})$. Each set $\mathbb{R} \setminus \{r\}$ is open, because a point is closed, and dense, because a point has empty interior. The intersection is countable, because $\mathbb{Q}$ is countable. $\square$

::: mathlib
`dense_irrational` · `Mathlib.Topology.Instances.Irrational`

`Dense {x : ℝ | Irrational x}`. The residual form is `eventually_residual_irrational : ∀ᶠ x in residual ℝ, Irrational x`. Mathlib expresses "residual" as a filter, so a Baire generic property uses the same `∀ᶠ` notation as "for all large `n`". The same file has `Irrational.eventually_forall_le_dist_cast_div`: an irrational number keeps a positive distance from the fractions with one fixed denominator.

<?decl dense_irrational?>
:::

### Examples

**Example (The proof for e with numbers).** Take $n = 4$. Then $s_4 = 1 + 1 + \frac12 + \frac16 = \frac83 = 2.666667$ and $e - s_4 = 0.051615$. So $3!\,(e - s_4) = 0.309691$. The lemma predicts $\frac14 \le 0.309691 \le \frac{5}{16} = 0.3125$. If $e$ were $a/b$ with $b \le 3$, then $6e - 16$ would be an integer in $(0, 1)$. So $e$ is not a fraction with denominator $1$, $2$ or $3$.

**Example (How large n must be).** Test Niven's bound with $a = 22$, $b = 7$, the approximation $22/7$. The proof needs $\pi(22\pi)^n/n! < 1$, with $22\pi \approx 69.1$. A computation with logarithms gives $n = 186$ as the first such $n$, so $f$ has degree $372$. The proof only uses that $n!$ eventually wins.

**Counterexample (Sums of irrationals).** The set of irrationals is not closed under addition: $\sqrt2$ and $-\sqrt2$ are irrational, and their sum is $0$. So nothing follows about $e + \pi$, whose irrationality is an open problem. Mathlib reflects the true statement: `Irrational.add_cases` says that if $x + y$ is irrational, then $x$ or $y$ is.

**Example (Irrationals from one irrational).** If $\pi - 3 = p/q$, then $\pi = (p + 3q)/q$ is rational. So $\pi - 3$ is irrational. In Mathlib this step is `irrational_pi.sub_intCast 3`, of type `Irrational (π - 3)`, from `Irrational.sub_intCast`.

### The library around it

`irrational_pi` is the only irrationality result of the analysis library. The arithmetic theory of `Irrational` is in Volume 12, with `irrational_sqrt_two`, `irrational_nrt_of_notint_nrt` and `Transcendental.irrational`. A search of the index at this commit finds no declaration that states the irrationality or the transcendence of `Real.exp 1`, and no transcendence result for `π`. The bounds `Real.exp_one_gt_d9` and `Real.exp_one_lt_d9` locate $e$ only.

Common errors of a learner:

- `Irrational x` is a negation. To use a hypothesis `h : Irrational x`, apply it to a proof that `x` is the cast of a rational number, and obtain `False`.
- The cast matters. A goal stated in `ℚ` or `ℕ` must be moved to `ℝ` before these lemmas apply.
- In Niven's proof the bound $0 < G(\pi) - G(0)$ needs $a, b > 0$.
- Residual does not mean large in measure. The rationals are meagre and of measure zero, but there are meagre sets of full measure.

### Exercises

1. (A) Prove that $\sqrt2 + \pi$ or $\sqrt2 - \pi$ is irrational. Hint: their sum is $2\sqrt2$.
2. (A) Show that $1/\pi$ and $2\pi + 1$ are irrational. Hint: rational numbers form a field.
3. (B) Prove that $e^2$ is irrational. Hint: if $e^2 = a/b$, then $b e = a e^{-1}$. Multiply by $n!/2^{n-1}$ for suitable $n$ and use the series of $e$ and $e^{-1}$ with their signs.
4. (B) Prove that $\cos 1$ is irrational with the method for $e$. Hint: the tail of the alternating series $\sum (-1)^k/(2k)!$ is bounded by its first term and has its sign.
5. (B) Show that in Niven's proof $\pi\, f(x) \sin x \le \pi \cdot \frac{(a^2/4b)^n}{n!}$, using that $x(a - bx)$ has its maximum at $x = a/(2b)$. Recompute the $n$ of the second example with this bound.
6. (C) Modify Niven's proof to show that $\pi^2$ is irrational. Hint: suppose $\pi^2 = a/b$, and use $G(x) = b^n(F'(x)\sin \pi x - \pi F(x) \cos \pi x)$ with $f(x) = x^n(1 - x)^n/n!$ on $[0, 1]$ and $F = \sum_k (-1)^k \pi^{2n-2k} f^{(2k)}$.
### Notes and history

Euler proved the irrationality of $e$ in 1737 with its continued fraction. The series proof is due to Fourier (published 1815). Lambert proved the irrationality of $\pi$ in 1761 with a continued fraction for $\tan x$. Hermite proved the transcendence of $e$ in 1873, and Lindemann that of $\pi$ in 1882. Niven's one page proof appeared in the *Bulletin of the American Mathematical Society* in 1947.

### Reference

<?reference?>
