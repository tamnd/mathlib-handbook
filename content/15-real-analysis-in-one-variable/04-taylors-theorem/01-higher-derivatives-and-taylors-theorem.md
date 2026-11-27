---
title: Higher derivatives and Taylor's theorem
kind: theory
modules:
  - Mathlib.Analysis.Calculus.IteratedDeriv.Defs
  - Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
explains:
  E3: [iteratedDeriv, iteratedDerivWithin]
  E2: [iteratedDeriv_succ, iteratedDeriv_eq_iterate, iteratedDerivWithin_succ, iteratedDerivWithin_eq_iteratedDeriv, contDiff_iff_iteratedDeriv, iteratedDeriv_pow]
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

## Higher derivatives and Taylor's theorem

### Overview

The tangent line $f(x_0) + f'(x_0)(x - x_0)$ is the best affine approximation of $f$ near $x_0$. If $f$ has more derivatives, a polynomial of higher degree gives a better approximation. The Taylor polynomial of degree $n$ is the polynomial whose value and first $n$ derivatives at $x_0$ agree with those of $f$. Taylor's theorem gives the error: there is a point $\xi$ between $x_0$ and $x$ with
$$f(x) = \sum_{k=0}^{n} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k + \frac{f^{(n+1)}(\xi)}{(n+1)!}(x - x_0)^{n+1}.$$
For $n = 0$ this is the mean value theorem. The proof for general $n$ is the Cauchy mean value theorem applied to a function of the base point, not of $x$.

This section defines the higher derivatives and the Taylor polynomial, and proves Taylor's theorem with the Lagrange, the Cauchy and the Peano remainder.

### Definitions

**Definition (Higher derivatives).** Let $I$ be an open interval and $f : I \to \mathbb{R}$. Set $f^{(0)} = f$. If $f^{(n)}$ is defined and differentiable on $I$, set $f^{(n+1)} = (f^{(n)})'$. The function $f$ is *$n$ times differentiable* on $I$ if $f^{(n)}$ exists on $I$. It is *of class $C^n$* on $I$ if also $f^{(n)}$ is continuous. It is *of class $C^\infty$*, or *smooth*, if it is of class $C^n$ for every $n$.

An $n$ times differentiable function is of class $C^{n-1}$, since a differentiable function is continuous. The class $C^n$ adds the continuity of the last derivative.

::: mathlib
`iteratedDeriv` · `Mathlib.Analysis.Calculus.IteratedDeriv.Defs`

The $n$-th derivative of `f : 𝕜 → F`. It is defined as `iteratedFDeriv 𝕜 n f x (fun _ ↦ 1)`, so that the one-variable theory is a special case of Volume 17. The recursion is `iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f)`, and `iteratedDeriv_eq_iterate` gives `deriv^[n] f`. Like `deriv`, the function is total: where the derivative does not exist, its value is `0`. The class $C^n$ is `ContDiff 𝕜 n f`, with the order in `WithTop ℕ∞`, and `contDiff_iff_iteratedDeriv` gives its one-variable meaning.

<?decl iteratedDeriv?>
:::

**Definition (Derivatives within a set).** For $s \subseteq \mathbb{R}$ and $x \in s$, the *derivative within $s$* is the limit of $(f(y) - f(x))/(y - x)$ as $y \to x$ with $y \in s \setminus \{x\}$. For $s = [a, b]$ and $x = a$ it is the right derivative.

::: mathlib
`iteratedDerivWithin` · `Mathlib.Analysis.Calculus.IteratedDeriv.Defs`

The $n$-th derivative within `s`, with `iteratedDerivWithin_succ` as recursion. Taylor's theorem in Mathlib uses it on `Set.uIcc x₀ x`, so no hypothesis on $f$ outside the interval is needed. On an interval and at a point where `f` is $C^n$, it agrees with `iteratedDeriv`: `iteratedDerivWithin_eq_iteratedDeriv`. In Mathlib the Taylor polynomial is `taylorWithinEval f n s x₀ x`.

<?decl iteratedDerivWithin?>
:::

**Definition (Taylor polynomial).** Let $f$ be $n$ times differentiable at $x_0$. The *Taylor polynomial of degree $n$ of $f$ at $x_0$* is
$$P_n(x) = \sum_{k=0}^{n} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k.$$
The *remainder* is $R_n(x) = f(x) - P_n(x)$.

The $k$-th derivative of $(x - x_0)^j$ at $x_0$ is $k!$ if $j = k$ and $0$ otherwise. So $P_n^{(k)}(x_0) = f^{(k)}(x_0)$ for $0 \le k \le n$.

### Theorems and proofs

The proof of Taylor's theorem fixes the point $x$ and moves the base point. Let $f$ be $n + 1$ times differentiable, and define, for $t$ between $x_0$ and $x$,
$$F(t) = \sum_{k=0}^{n} \frac{f^{(k)}(t)}{k!}(x - t)^k.$$
At the two ends, $F(x_0) = P_n(x)$ and $F(x) = f(x)$, because every term with $k \ge 1$ has the factor $(x - x)^k = 0$. So $R_n(x) = F(x) - F(x_0)$, and the mean value theorem applies to this difference.

**Lemma (The derivative of the Taylor polynomial in the base point).** Let $J$ be an open interval, let $x \in \mathbb{R}$, and let $f$ be $n + 1$ times differentiable on $J$. Then $F$ is differentiable on $J$ and
$$F'(t) = \frac{f^{(n+1)}(t)}{n!}(x - t)^n.$$

*Proof.* Differentiate $F$ term by term with the product rule. The term $k = 0$ is $f(t)$, with derivative $f'(t)$. For $1 \le k \le n$,
$$\frac{d}{dt}\left[\frac{f^{(k)}(t)}{k!}(x - t)^k\right] = \frac{f^{(k+1)}(t)}{k!}(x - t)^k - \frac{f^{(k)}(t)}{(k-1)!}(x - t)^{k-1},$$
because the derivative of $(x - t)^k$ in $t$ is $-k(x - t)^{k-1}$ and $k/k! = 1/(k-1)!$. Put $a_k = \frac{f^{(k+1)}(t)}{k!}(x - t)^k$ for $0 \le k \le n$. The derivative of the term $k$ is $a_k - a_{k-1}$ for $k \ge 1$, and it is $a_0$ for $k = 0$. The sum telescopes:
$$F'(t) = a_0 + \sum_{k=1}^{n} (a_k - a_{k-1}) = a_n = \frac{f^{(n+1)}(t)}{n!}(x - t)^n. \qquad \square$$

**Theorem (Taylor's theorem with a general remainder).** Let $x_0 \ne x$ and let $I$ be the closed interval with end points $x_0$ and $x$, with interior $I^\circ$. Assume that $f$ is of class $C^n$ on $I$ and that $f^{(n)}$ is differentiable on $I^\circ$. Let $g$ be continuous on $I$ and differentiable on $I^\circ$ with $g'(t) \ne 0$ for $t \in I^\circ$. Then there is $\xi \in I^\circ$ with
$$f(x) - P_n(x) = \frac{f^{(n+1)}(\xi)}{n!}(x - \xi)^n \cdot \frac{g(x) - g(x_0)}{g'(\xi)}.$$

*Proof.* The plan: check that $F$ satisfies the hypotheses of the Cauchy mean value theorem on $I$, then apply that theorem to $F$ and $g$.

Step 1: $F$ is continuous on $I$. Each $f^{(k)}$ with $k \le n$ is continuous on $I$, since $f$ is of class $C^n$ there. Each $(x - t)^k$ is continuous. So $F$, a finite sum of products, is continuous on $I$.

Step 2: $F$ is differentiable on $I^\circ$ with the derivative of the lemma. For $k < n$ the function $f^{(k)}$ is differentiable on $I$, with derivative $f^{(k+1)}$. For $k = n$ the function $f^{(n)}$ is differentiable on $I^\circ$ by hypothesis. So the computation of the lemma holds at each $t \in I^\circ$.

Step 3: the Cauchy mean value theorem of Chapter 3 gives $\xi \in I^\circ$ with
$$\big(F(x) - F(x_0)\big) g'(\xi) = \big(g(x) - g(x_0)\big) F'(\xi).$$
Here $F(x) - F(x_0) = f(x) - P_n(x)$. Divide by $g'(\xi) \ne 0$ and insert $F'(\xi)$ from the lemma. $\square$

The choice of $g$ gives the classical forms.

**Theorem (Taylor's theorem with the Lagrange remainder).** Under the hypotheses on $f$ of the last theorem, there is $\xi$ strictly between $x_0$ and $x$ with
$$f(x) = \sum_{k=0}^{n} \frac{f^{(k)}(x_0)}{k!}(x - x_0)^k + \frac{f^{(n+1)}(\xi)}{(n+1)!}(x - x_0)^{n+1}.$$

*Proof.* Take $g(t) = (x - t)^{n+1}$. It is continuous, and $g'(t) = -(n+1)(x - t)^n$, which is not $0$ for $t \ne x$, so on $I^\circ$. Also $g(x) - g(x_0) = 0 - (x - x_0)^{n+1}$. The general theorem gives
$$f(x) - P_n(x) = \frac{f^{(n+1)}(\xi)}{n!}(x - \xi)^n \cdot \frac{-(x - x_0)^{n+1}}{-(n+1)(x - \xi)^n} = \frac{f^{(n+1)}(\xi)}{(n+1)!}(x - x_0)^{n+1},$$
since $(n+1) \cdot n! = (n+1)!$. $\square$

**Theorem (Taylor's theorem with the Cauchy remainder).** Under the same hypotheses there is $\xi$ strictly between $x_0$ and $x$ with
$$f(x) - P_n(x) = \frac{f^{(n+1)}(\xi)}{n!}(x - \xi)^n (x - x_0).$$

*Proof.* Take $g(t) = t$. Then $g' = 1$ and $g(x) - g(x_0) = x - x_0$. $\square$

::: mathlib
`taylor_mean_remainder_lagrange` · `Mathlib.Analysis.Calculus.Taylor`

The Lagrange form. The hypotheses are `x₀ ≠ x`, `ContDiffOn ℝ n f (Set.uIcc x₀ x)` and the differentiability of `iteratedDerivWithin n f (Set.uIcc x₀ x)` on `Set.uIoo x₀ x`. The intervals `uIcc` and `uIoo` allow $x < x_0$. The Cauchy form is `taylor_mean_remainder_cauchy`, and `taylor_mean_remainder_bound` gives a bound with $n!$ in place of $(n+1)!$, because it holds for any normed codomain.

<?decl taylor_mean_remainder_lagrange?>
:::

A weaker statement needs only $n$ derivatives.

**Theorem (Taylor's theorem with the Peano remainder).** Let $I$ be an interval, $x_0 \in I$, $n \ge 1$, and let $f$ be of class $C^n$ on $I$. Then
$$\lim_{x \to x_0,\, x \in I} \frac{f(x) - P_n(x)}{(x - x_0)^n} = 0.$$

*Proof.* Let $x \in I$ with $x \ne x_0$. Apply the Lagrange form of degree $n - 1$. Its hypotheses hold: $f$ is of class $C^{n-1}$, and $f^{(n-1)}$ is differentiable with derivative $f^{(n)}$. So there is $\xi_x$ strictly between $x_0$ and $x$ with
$$f(x) = P_{n-1}(x) + \frac{f^{(n)}(\xi_x)}{n!}(x - x_0)^n.$$
Subtract $P_n(x) = P_{n-1}(x) + \frac{f^{(n)}(x_0)}{n!}(x - x_0)^n$. This gives
$$\frac{f(x) - P_n(x)}{(x - x_0)^n} = \frac{f^{(n)}(\xi_x) - f^{(n)}(x_0)}{n!}.$$
Let $\varepsilon > 0$. The function $f^{(n)}$ is continuous at $x_0$, so there is $\delta > 0$ with $|f^{(n)}(y) - f^{(n)}(x_0)| < n!\,\varepsilon$ for $y \in I$ and $|y - x_0| < \delta$. If $0 < |x - x_0| < \delta$, then $|\xi_x - x_0| < |x - x_0| < \delta$, so the quotient has absolute value less than $\varepsilon$. $\square$

In the language of Chapter 7 this is $f(x) - P_n(x) = o\big((x - x_0)^n\big)$. Exercise 6 treats a function that is twice differentiable at one point only.

::: mathlib
`taylor_isLittleO` · `Mathlib.Analysis.Calculus.Taylor`

The Peano form: for a convex set `s` with `x₀ ∈ s` and `ContDiffOn ℝ n f s`, the function `fun x ↦ f x - taylorWithinEval f n s x₀ x` is `=o[nhdsWithin x₀ s]` of `fun x ↦ (x - x₀) ^ n`. The filter `nhdsWithin x₀ s` is the limit $x \to x_0$ with $x \in s$, and the convex sets of $\mathbb{R}$ are the intervals.

<?decl taylor_isLittleO?>
:::

### Examples

**Example (The Taylor polynomials of the exponential).** Let $f = \exp$ and $x_0 = 0$. Each derivative of $\exp$ is $\exp$, and $\exp(0) = 1$, so
$$P_n(x) = \sum_{k=0}^{n} \frac{x^k}{k!}.$$
For $x = 1$ the Lagrange form gives $\xi \in (0, 1)$ with $e - P_n(1) = \frac{e^\xi}{(n+1)!}$. With $1 < e^\xi < e < 3$,
$$\frac{1}{(n+1)!} < e - \sum_{k=0}^{n} \frac{1}{k!} < \frac{3}{(n+1)!}.$$
For $n = 6$ the sum is $\frac{1957}{720} = 2.718055\ldots$, and $3/7! < 0.000596$. The true error is $0.000226$, between $1/7! = 0.000198$ and $0.000596$.

**Counterexample (The derivative of order $n + 1$ is needed on the whole open interval).** Let $f(x) = x|x|$. Then $f'(x) = 2|x|$ for all $x$, so $f$ is of class $C^1$, but $f'$ is not differentiable at $0$. Take $x_0 = -1$ and $x = 1$, with $n = 1$. Then $P_1(x) = f(-1) + f'(-1)(x + 1) = -1 + 2(x + 1)$, so $P_1(1) = 3$ and $f(1) - P_1(1) = -2$. The Lagrange form would give $\xi \in (-1, 1)$ with $\frac{f''(\xi)}{2} \cdot 2^2 = -2$, that is, $f''(\xi) = -1$. But $f''(\xi) = -2$ for $\xi < 0$, $f''(\xi) = 2$ for $\xi > 0$, and $f''(0)$ does not exist. So no such $\xi$ exists. The theorem fails because $f'$ is not differentiable at the single point $0$ of the open interval. In Mathlib the hypothesis `DifferentiableOn ℝ (iteratedDerivWithin 1 f _) (Set.uIoo (-1) 1)` is false here.

### The library around it

The file `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas` has the algebra of iterated derivatives, for example `iteratedDeriv_const_mul`, `iteratedDeriv_comp_const_mul` and `iteratedDeriv_pow`, which gives the $k$-th derivative of $x^m$ as `m.descFactorial k * x ^ (m - k)`. Most of these lemmas need a `ContDiffAt` hypothesis, because of the junk values. Taylor's theorem is in `Mathlib.Analysis.Calculus.Taylor` of Volume 17.

Common errors of a learner:

- The Taylor polynomial in Mathlib uses derivatives *within* the interval. The lemma `iteratedDerivWithin_eq_iteratedDeriv` converts them to global derivatives, and it needs `UniqueDiffOn ℝ s` and `ContDiffAt` at the point. For a nontrivial interval, `uniqueDiffOn_Icc` gives the first hypothesis.
- The order of `ContDiff` is in `WithTop ℕ∞`. A natural number appears as the cast `(n : WithTop ℕ∞)`, `∞` means smooth and `ω` means analytic. `ContDiff ℝ ⊤ f` is the analytic class.
- At a point of non-differentiability, `iteratedDeriv` is `0` in Lean. The hypotheses `ContDiffOn` and `DifferentiableOn` of the theorems exclude these junk values.

### Exercises

1. (A) Compute the Taylor polynomial of degree $4$ of $\cos$ at $0$, and of $x \mapsto 1/(1 - x)$ at $0$.
2. (A) Use the Lagrange form to show that $|\cos x - 1 + x^2/2| \le x^4/24$ for all $x \in \mathbb{R}$. Hint: take $n = 3$ and note that $\cos'''(0) = 0$.
3. (B) Show that $e^x > 1 + x + x^2/2$ for all $x > 0$, and that the inequality is false for every $x < 0$. Hint: the remainder of degree $2$ is $e^\xi x^3/6$.
4. (B) Let $f$ be of class $C^2$ on $\mathbb{R}$. Prove that $f''(x_0) = \lim_{h \to 0} \frac{f(x_0 + h) - 2 f(x_0) + f(x_0 - h)}{h^2}$. Hint: apply the Peano form of degree $2$ at $x_0 + h$ and at $x_0 - h$, and add.
5. (B) Find the smallest $n$ such that $\sum_{k=0}^{n} 1/k!$ approximates $e$ with an error less than $10^{-9}$. Hint: use the two sided bound of the first example.
6. (C) Let $f'$ exist on an interval around $x_0$ and be differentiable at $x_0$. Prove that $f(x) - P_2(x) = o((x - x_0)^2)$ as $x \to x_0$. Hint: apply l'Hôpital's rule of Chapter 3 once, then use the definition of $f''(x_0)$.

### Notes and history

Brook Taylor published the series in 1715. James Gregory and Newton knew it earlier. The remainder with $f^{(n+1)}(\xi)$ is due to Lagrange (1797), the Cauchy form to Cauchy (1823), and the Peano form to Peano (1884). In Mathlib, `Mathlib.Analysis.Calculus.Taylor` is by Moritz Doll (2022), and its proof is the one of this section.

### Reference

<?reference?>
