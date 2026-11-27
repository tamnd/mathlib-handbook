---
title: Applications of Taylor's theorem
kind: theory
modules:
  - Mathlib.Analysis.Calculus.DerivativeTest
explains:
  E3: [isLocalMin_of_deriv_deriv_pos]
  E2: [isLocalMax_of_deriv_deriv_neg, isLocalMin_of_deriv, isLocalMax_of_deriv]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C02, V15.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Applications of Taylor's theorem

### Overview

Taylor's theorem of Section 1 writes a function near $x_0$ as its Taylor polynomial plus a remainder. This section uses it in four ways: the derivatives at a critical point decide whether it is a minimum, a maximum or neither; $f'' \ge 0$ gives convexity; the remainder gives numerical bounds such as $|\sin x - x + x^3/6| \le |x|^5/120$; and when the remainders tend to $0$, the function is the sum of its Taylor series. The last statement holds for $\exp$, $\sin$ and $\cos$, and fails for some smooth functions.

### Definitions

**Definition (Local extremum).** Let $f : \mathbb{R} \to \mathbb{R}$ and $x_0 \in \mathbb{R}$. The point $x_0$ is a *local minimum* of $f$ if there is $\delta > 0$ with $f(x_0) \le f(x)$ for all $x$ with $|x - x_0| < \delta$. It is a *strict local minimum* if also $f(x_0) < f(x)$ for $0 < |x - x_0| < \delta$. Local maxima are defined with the inequalities reversed. A *critical point* is a point $x_0$ with $f'(x_0) = 0$.

Fermat's theorem of Chapter 3 says that $f'(x_0) = 0$ at a local extremum where $f$ is differentiable. The converse is false, as $x^3$ at $0$ shows.

**Definition (Convex function).** Let $I$ be an interval. A function $f : I \to \mathbb{R}$ is *convex* if for all $x, y \in I$ and $t \in [0, 1]$,
$$f(tx + (1 - t)y) \le t f(x) + (1 - t) f(y).$$
It is *strictly convex* if the inequality is strict for $x \ne y$ and $0 < t < 1$.

**Definition (Taylor series, analytic function).** Let $f$ be smooth on an open interval that contains $x_0$. The *Taylor series* of $f$ at $x_0$ is the power series $\sum_{k \ge 0} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k$. The function $f$ is *analytic at $x_0$* if there is $r > 0$ such that the series converges to $f(x)$ for all $x$ with $|x - x_0| < r$.

The partial sums of the series are the $P_n$, so the series converges to $f(x)$ if and only if $R_n(x) \to 0$.

### Theorems and proofs

**Theorem (Second derivative test).** Let $f$ be differentiable on an open interval around $x_0$, with $f'(x_0) = 0$, and let $f'$ be differentiable at $x_0$ with $f''(x_0) > 0$. Then $x_0$ is a strict local minimum of $f$. If $f''(x_0) < 0$, then $x_0$ is a strict local maximum.

*Proof.* Assume $f''(x_0) > 0$. By definition and by $f'(x_0) = 0$,
$$f''(x_0) = \lim_{x \to x_0} \frac{f'(x) - f'(x_0)}{x - x_0} = \lim_{x \to x_0} \frac{f'(x)}{x - x_0}.$$
The limit is positive, so there is $\delta > 0$ such that $f$ is differentiable on $(x_0 - \delta, x_0 + \delta)$ and $f'(x)/(x - x_0) > 0$ for $0 < |x - x_0| < \delta$. Thus $f'(x) < 0$ for $x_0 - \delta < x < x_0$, and $f'(x) > 0$ for $x_0 < x < x_0 + \delta$.

Let $x_0 < x < x_0 + \delta$. The mean value theorem of Chapter 3 gives $\eta \in (x_0, x)$ with $f(x) - f(x_0) = f'(\eta)(x - x_0)$. Both factors are positive, so $f(x) > f(x_0)$. Let $x_0 - \delta < x < x_0$. The mean value theorem gives $\eta \in (x, x_0)$ with $f(x) - f(x_0) = f'(\eta)(x - x_0)$. Both factors are negative, so again $f(x) > f(x_0)$. For $f''(x_0) < 0$, apply this to $-f$. $\square$

When $f''(x_0) = 0$ the test says nothing: $x^4$, $-x^4$ and $x^3$ have $f'(0) = f''(0) = 0$, and $0$ is a minimum, a maximum and neither. The next theorem handles these cases.

::: mathlib
`isLocalMin_of_deriv_deriv_pos` · `Mathlib.Analysis.Calculus.DerivativeTest`

The second derivative test: `deriv (deriv f) x₀ > 0 → deriv f x₀ = 0 → ContinuousAt f x₀ → IsLocalMin f x₀`. There is no hypothesis of differentiability near `x₀`, because of the junk values: `deriv (deriv f) x₀ ≠ 0` forces `deriv f` to be differentiable at `x₀`, and then `deriv f x ≠ 0` near `x₀`, which forces `f` to be differentiable at `x`. The first derivative test is `isLocalMin_of_deriv`, with sign conditions on `deriv f` along `nhdsWithin b (Set.Iio b)` and `nhdsWithin b (Set.Ioi b)`. The forms for a maximum are `isLocalMax_of_deriv` and `isLocalMax_of_deriv_deriv_neg`.

<?decl isLocalMin_of_deriv_deriv_pos?>
:::

**Theorem (Higher derivative test).** Let $n \ge 2$ and let $f$ be of class $C^n$ on an open interval around $x_0$, with $f^{(k)}(x_0) = 0$ for $1 \le k \le n - 1$ and $f^{(n)}(x_0) \ne 0$.

1. If $n$ is even and $f^{(n)}(x_0) > 0$, then $x_0$ is a strict local minimum.
2. If $n$ is even and $f^{(n)}(x_0) < 0$, then $x_0$ is a strict local maximum.
3. If $n$ is odd, then $x_0$ is not a local extremum.

*Proof.* By continuity there is $\delta > 0$ such that $f^{(n)}$ has the sign of $f^{(n)}(x_0)$ on $(x_0 - \delta, x_0 + \delta)$, and $f$ is $C^n$ there. Let $0 < |x - x_0| < \delta$. The Lagrange form of degree $n - 1$ applies: $f$ is $C^{n-1}$ and $f^{(n-1)}$ is differentiable. It gives $\xi$ strictly between $x_0$ and $x$ with
$$f(x) = \sum_{k=0}^{n-1} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k + \frac{f^{(n)}(\xi)}{n!}(x - x_0)^n = f(x_0) + \frac{f^{(n)}(\xi)}{n!}(x - x_0)^n,$$
since the terms with $1 \le k \le n - 1$ are $0$. Also $|\xi - x_0| < \delta$, so $f^{(n)}(\xi)$ has the sign of $f^{(n)}(x_0)$.

If $n$ is even, then $(x - x_0)^n > 0$, so $f(x) - f(x_0)$ has the sign of $f^{(n)}(x_0)$ for every such $x$. This proves 1 and 2. If $n$ is odd, then $(x - x_0)^n$ has the sign of $x - x_0$. So $f(x) - f(x_0)$ has one sign for $x > x_0$ and the opposite sign for $x < x_0$, and in every neighbourhood of $x_0$ there are points with $f(x) > f(x_0)$ and points with $f(x) < f(x_0)$. This proves 3. $\square$

**Theorem (Convexity from the second derivative).** Let $I$ be an open interval and let $f$ be twice differentiable on $I$ with $f'' \ge 0$ on $I$. Then $f$ is convex on $I$. If $f'' > 0$ on $I$, then $f$ is strictly convex.

*Proof.* Step 1: the tangent inequality. Let $z, y \in I$ with $y \ne z$. Here $f$ is $C^1$, since $f'$ is differentiable. The Lagrange form of degree $1$ at the base point $z$ gives $\xi$ between $z$ and $y$ with
$$f(y) = f(z) + f'(z)(y - z) + \frac{f''(\xi)}{2}(y - z)^2 \ge f(z) + f'(z)(y - z).$$
It is strict if $f'' > 0$.

Step 2: the convexity inequality. Let $x, y \in I$, $t \in [0, 1]$ and $z = tx + (1 - t)y \in I$. Step 1 at the points $x$ and $y$ gives
$$f(x) \ge f(z) + f'(z)(x - z), \qquad f(y) \ge f(z) + f'(z)(y - z).$$
Multiply the first inequality by $t \ge 0$ and the second by $1 - t \ge 0$, and add:
$$t f(x) + (1 - t) f(y) \ge f(z) + f'(z)\big(tx + (1 - t)y - z\big) = f(z).$$
If $f'' > 0$, $x \ne y$ and $0 < t < 1$, then $x \ne z$ and $y \ne z$, both inequalities are strict, and both coefficients are positive, so the sum is strict. $\square$

::: mathlib
`convexOn_of_deriv2_nonneg` · `Mathlib.Analysis.Convex.Deriv`

The hypotheses are `Convex ℝ D`, `ContinuousOn f D`, the differentiability of `f` and of `deriv f` on `interior D`, and `0 ≤ deriv^[2] f x` on `interior D`. The conclusion is `ConvexOn ℝ D f`. The proof in Mathlib shows that `deriv f` is monotone, with no Taylor's theorem. The strict form is `strictConvexOn_of_deriv2_pos`.

<?decl convexOn_of_deriv2_nonneg?>
:::

**Theorem (A bound for the sine).** For all $x \in \mathbb{R}$,
$$\left| \sin x - x + \frac{x^3}{6} \right| \le \frac{|x|^5}{120}.$$

*Proof.* The derivatives of $\sin$ repeat with period $4$: $\sin, \cos, -\sin, -\cos$. At $0$ their values are $0, 1, 0, -1$. So the Taylor polynomial of degree $4$ at $0$ is
$$P_4(x) = 0 + x + 0 - \frac{x^3}{6} + 0 = x - \frac{x^3}{6}.$$
The term of degree $4$ is $0$ because $\sin^{(4)}(0) = 0$. The Lagrange form of degree $4$ gives $\xi$ between $0$ and $x$ with $\sin x - P_4(x) = \frac{\cos \xi}{120} x^5$, and $|\cos \xi| \le 1$. $\square$

At $x = 0.5$ the bound is $0.5^5/120 = 0.00026042$, and the true error is $\sin 0.5 - 0.4791667 = 0.0002588$. Mathlib's `Real.sin_bound` has the constant $100$ for $|x| \le 1$, because it is proved from the power series before the derivative of $\sin$ exists.

**Lemma (The factorial beats the power).** For each $a \ge 0$, $\lim_{n \to \infty} a^n / n! = 0$.

*Proof.* Choose an integer $N \ge 2a$ and put $c = a^N / N!$. For $n \ge N$, $\frac{a^{n+1}}{(n+1)!} = \frac{a}{n+1} \cdot \frac{a^n}{n!} \le \frac12 \cdot \frac{a^n}{n!}$, since $n + 1 > N \ge 2a$. By induction, $0 \le a^n/n! \le c\, 2^{-(n - N)}$ for $n \ge N$. The right side tends to $0$, and the squeeze theorem of Chapter 1 gives the limit. $\square$

**Theorem (The exponential, sine and cosine series).** For every $x \in \mathbb{R}$,
$$e^x = \sum_{k=0}^{\infty} \frac{x^k}{k!}, \qquad \sin x = \sum_{k=0}^{\infty} \frac{(-1)^k x^{2k+1}}{(2k+1)!}, \qquad \cos x = \sum_{k=0}^{\infty} \frac{(-1)^k x^{2k}}{(2k)!}.$$

*Proof.* For $\exp$, every derivative is $\exp$, so $P_n(x) = \sum_{k \le n} x^k/k!$, as in Section 1. The Lagrange form gives $\xi$ between $0$ and $x$ with
$$\left| e^x - P_n(x) \right| = \frac{e^\xi |x|^{n+1}}{(n+1)!} \le e^{|x|} \frac{|x|^{n+1}}{(n+1)!}.$$
By the lemma with $a = |x|$, the right side tends to $0$. For $\sin$ and $\cos$, every derivative is $\pm \sin$ or $\pm \cos$, so the remainder is at most $|x|^{n+1}/(n+1)!$. $\square$

In Mathlib the series of $e^x$ is the definition: `NormedSpace.exp_eq_tsum_div` and `Real.exp_eq_exp_ℝ`. The theorem above is the opposite direction.

### Examples

**Example (Classifying critical points).** Let $f(x) = \cos x - 1 + x^2/2$ at $x_0 = 0$. The derivatives are $f'(x) = -\sin x + x$, $f''(x) = 1 - \cos x$, $f'''(x) = \sin x$ and $f^{(4)}(x) = \cos x$. At $0$ the values are $0, 0, 0, 1$. So $n = 4$ is even with $f^{(4)}(0) = 1 > 0$, and $0$ is a strict local minimum: $\cos x > 1 - x^2/2$ for small $x \ne 0$. Let $h(x) = \sin x - x$. Then $h'(0) = \cos 0 - 1 = 0$, $h''(0) = -\sin 0 = 0$ and $h'''(0) = -\cos 0 = -1$. So $n = 3$ is odd, and $0$ is not a local extremum of $h$. Indeed, $h(x) < 0$ for $x > 0$ and $h(x) > 0$ for $x < 0$.

**Example (Convexity and the mean inequality).** $\exp'' = \exp > 0$, so $\exp$ is strictly convex, and its tangent at $0$ gives $e^y \ge 1 + y$ (`Real.add_one_le_exp`). The function $-\log$ has second derivative $1/x^2 > 0$ on $(0, \infty)$. Convexity with $t = \frac12$ gives $\log\frac{x+y}{2} \ge \frac12(\log x + \log y)$, that is, $\frac{x+y}{2} \ge \sqrt{xy}$.

**Counterexample (A smooth function that is not analytic).** Let $g(x) = e^{-1/x}$ for $x > 0$ and $g(x) = 0$ for $x \le 0$. For $x > 0$, induction gives $g^{(n)}(x) = p_n(1/x)e^{-1/x}$ with polynomials $p_0 = 1$, $p_{n+1}(y) = y^2(p_n(y) - p_n'(y))$. Since $y^k e^{-y} \to 0$ as $y \to \infty$, the one-sided difference quotients at $0$ tend to $0$, and by induction $g$ is smooth with $g^{(n)}(0) = 0$ for all $n$. So every Taylor polynomial at $0$ is $0$, but $g(0.1) = e^{-10} = 0.0000454 > 0$. The remainder $R_n(0.1) = e^{-10}$ does not tend to $0$. In Mathlib, $g$ is `expNegInvGlue`, with `expNegInvGlue.contDiff`. Volume 17 builds the bump functions from it.

### The library around it

The file `Mathlib.Analysis.Calculus.DerivativeTest` has `isLocalMin_of_deriv`, `isLocalMax_of_deriv`, `isLocalMin_of_deriv_deriv_pos` and `isLocalMax_of_deriv_deriv_neg`. Mathlib has no higher derivative test. A proof follows the text, with `taylor_mean_remainder_lagrange`.

The convexity results are in `Mathlib.Analysis.Convex.Deriv` of Volume 16. The bounds `Real.exp_bound`, `Real.sin_bound` and `Real.cos_bound` are in Volume 19.

Common errors of a learner:

- The second derivative test needs $f'(x_0) = 0$. A point with $f''(x_0) > 0$ and $f'(x_0) \ne 0$ is not an extremum, and in Mathlib the hypothesis `deriv f x₀ = 0` is explicit.
- Convexity needs $f'' \ge 0$ on an interval. The function $1/x$ has $f'' > 0$ on $\mathbb{R} \setminus \{0\}$ and is not convex there. Mathlib asks for `Convex ℝ D`.
- A smooth function is not always the sum of its Taylor series. Show that the remainder tends to $0$. The series of $g$ above converges everywhere, to $0$.

### Exercises

1. (A) Find the critical points of $f(x) = x^4 - 2x^2$ and classify them with the second derivative test.
2. (A) Classify the critical point $0$ of $x \mapsto x^5$, of $x \mapsto x^6$ and of $x \mapsto x^2 \sin x$ with the higher derivative test.
3. (B) Prove that $1 - \frac{x^2}{2} \le \cos x \le 1 - \frac{x^2}{2} + \frac{x^4}{24}$ for all $x \in \mathbb{R}$. Hint: use the Lagrange form of degree $1$ for the left inequality and of degree $3$ for the right one. In both remainders the factor $\cos \xi$ appears, with $|\cos \xi| \le 1$.
4. (B) Let $f$ be twice differentiable on $\mathbb{R}$ with $|f''| \le M$. Assume that $f$ is bounded, with $S = \sup|f|$. Prove that $|f'(x)| \le \frac{S}{h} + \frac{Mh}{2}$ for every $x$ and every $h > 0$, and deduce $|f'(x)| \le \sqrt{2MS}$. Hint: apply the Lagrange form of degree $1$ at $x$ to $f(x + h)$ and to $f(x - h)$, and subtract.
5. (C) Prove that $g(x) = e^{-1/x^2}$ for $x \ne 0$ and $g(0) = 0$ is smooth with $g^{(n)}(0) = 0$ for all $n$. Hint: follow the counterexample and note that $g$ is even.

### Notes and history

The second derivative test is in Maclaurin's *Treatise of Fluxions* (1742). Lagrange based his calculus on Taylor series (1797), and Cauchy refuted the assumption that every function is analytic with $e^{-1/x^2}$ (1823). In Mathlib, `Mathlib.Analysis.Calculus.DerivativeTest` was started by Bjørn Kjos-Hanssen in 2024.

### Reference

<?reference?>
