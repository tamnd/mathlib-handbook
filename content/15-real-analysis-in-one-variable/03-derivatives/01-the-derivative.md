---
title: The derivative and the rules of differentiation
kind: theory
modules:
  - Mathlib.Analysis.Calculus.Deriv.Basic
  - Mathlib.Analysis.Calculus.Deriv.Slope
  - Mathlib.Analysis.Calculus.Deriv.Add
  - Mathlib.Analysis.Calculus.Deriv.Mul
  - Mathlib.Analysis.Calculus.Deriv.Comp
  - Mathlib.Analysis.Calculus.Deriv.Inv
  - Mathlib.Analysis.Calculus.Deriv.Pow
  - Mathlib.Analysis.Calculus.Deriv.Inverse
  - Mathlib.Analysis.Calculus.Deriv.Abs
explains:
  E3: [HasDerivAt, deriv, HasDerivAt.comp, HasDerivAt.mul]
  E2: [HasDerivAt.continuousAt, HasDerivAt.div, hasDerivAt_pow, HasDerivAt.of_local_left_inverse, deriv_abs]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The derivative and the rules of differentiation

### Overview

The derivative of a function at a point is the slope of the best linear approximation of the function near the point. It is a limit of difference quotients, so the limits of functions from Chapter 2 are the base of this section. The section proves the rules of differentiation: sum, product, quotient, chain, power and inverse function. The proofs use the criterion of Carathéodory, which writes the difference quotient as a function continuous at the point.

### Definitions

**Definition (Derivative).** Let $f$ be defined on an open interval that contains $a$. The function $f$ is *differentiable at $a$* if the limit
$$f'(a) = \lim_{x \to a} \frac{f(x) - f(a)}{x - a}$$
exists in $\mathbb{R}$, as a limit with $x \neq a$. The number $f'(a)$ is the *derivative* of $f$ at $a$, and the quotient is the *slope* of $f$ between $a$ and $x$. If $f$ is differentiable at each point of an open set $U$, then $x \mapsto f'(x)$ is the derivative $f'$ on $U$.

**Definition (Derivative within a set).** Let $a \in S$ be a limit point of $S \setminus \{a\}$. The number $L$ is a *derivative of $f$ at $a$ within $S$* if the slope tends to $L$ as $x \to a$ with $x \in S \setminus \{a\}$. For $S = [a, \infty)$ this is the *right derivative*, for $S = (-\infty, a]$ the *left derivative*.

The derivative within a set is the tool at an end point of $[a, b]$; in Mathlib it is `HasDerivWithinAt f f' s x`, with `s = Set.Ici a` for a right derivative. An equivalent form of the definition is the *linear approximation*: $f'(a) = L$ if and only if $f(x) = f(a) + L(x - a) + r(x)$ with $r(x)/(x - a) \to 0$, that is $r(x) = o(x - a)$ in the notation of Chapter 7.

::: mathlib
`HasDerivAt` · `Mathlib.Analysis.Calculus.Deriv.Basic`

`HasDerivAt f f' x` says that `f` has the derivative `f'` at `x`. It is a relation: the derivative is an argument. Mathlib states it in the linear approximation form, `f x' = f x + (x' - x) • f' + o(x' - x)`, for a function on any nontrivially normed field with values in a normed space. The textbook form is the theorem `hasDerivAt_iff_tendsto_slope`: `slope f x` tends to `f'` along `𝓝[≠] x`. It is a special case of the Fréchet derivative of Volume 17.

<?decl HasDerivAt?>
:::

**Definition (The derivative function in Mathlib).** For each $f : \mathbb{R} \to \mathbb{R}$ and each $x$, the number $\operatorname{deriv} f\, x$ is $f'(x)$ if $f$ is differentiable at $x$, and $0$ otherwise.

Mathlib prefers total functions, so `deriv f` takes the *junk value* $0$ where $f$ is not differentiable, as `x / 0 = 0` in a field. So an equation `deriv f x = c` carries no information unless `f` is differentiable at `x`.

::: mathlib
`deriv` · `Mathlib.Analysis.Calculus.Deriv.Basic`

`deriv f x` is the derivative of `f` at `x` if it exists, and `0` otherwise (`deriv_zero_of_not_differentiableAt`). The bridges are `HasDerivAt.deriv : HasDerivAt f f' x → deriv f x = f'` and `DifferentiableAt.hasDerivAt`. A proof usually works with `HasDerivAt`, which carries the value and needs no side condition, and converts to `deriv` at the end.

<?decl deriv?>
:::

### Theorems and proofs

**Theorem (Carathéodory's criterion).** Let $f$ be defined on an open interval $I \ni a$. Then $f$ is differentiable at $a$ if and only if there is $\varphi : I \to \mathbb{R}$, continuous at $a$, with $f(x) - f(a) = \varphi(x)(x - a)$ for all $x \in I$. Then $\varphi(a) = f'(a)$.

*Proof.* If $f'(a)$ exists, let $\varphi(x)$ be the slope for $x \neq a$ and $\varphi(a) = f'(a)$. The identity holds for $x \neq a$ by definition and for $x = a$ because both sides are $0$. The limit of $\varphi$ at $a$ is $f'(a) = \varphi(a)$, so $\varphi$ is continuous at $a$. Conversely, for $x \neq a$ the slope equals $\varphi(x)$, which tends to $\varphi(a)$. So $f'(a) = \varphi(a)$. $\square$

**Theorem (Differentiable implies continuous).** If $f$ is differentiable at $a$, then $f$ is continuous at $a$.

*Proof.* With $\varphi$ from the criterion, $f(x) = f(a) + \varphi(x)(x - a)$. As $x \to a$, $\varphi(x) \to \varphi(a)$ and $x - a \to 0$, so the product tends to $0$ by the product rule for limits. So $f(x) \to f(a)$. $\square$

::: mathlib
`HasDerivAt.continuousAt` · `Mathlib.Analysis.Calculus.Deriv.Basic`

`HasDerivAt f f' x → ContinuousAt f x`.

<?decl HasDerivAt.continuousAt?>
:::

**Theorem (Sum and product rules).** Let $f, g$ be differentiable at $a$ and $c \in \mathbb{R}$. Then $f + g$, $c f$ and $f g$ are differentiable at $a$, with $(f + g)'(a) = f'(a) + g'(a)$, $(c f)'(a) = c f'(a)$ and
$$(f g)'(a) = f'(a) g(a) + f(a) g'(a).$$

*Proof.* The slope of $f + g$ is the sum of the slopes, and the slope of $c f$ is $c$ times the slope of $f$; the sum rule for limits gives the first two claims. For the product, take $\varphi$ for $f$ and $\psi$ for $g$ from the criterion. Then
$$f(x) g(x) - f(a) g(a) = (f(x) - f(a)) g(x) + f(a)(g(x) - g(a)) = \big(\varphi(x) g(x) + f(a) \psi(x)\big)(x - a).$$
The function $\chi = \varphi g + f(a) \psi$ is continuous at $a$, because $g$ is continuous at $a$ by the previous theorem. By the criterion, $(f g)'(a) = \chi(a) = f'(a) g(a) + f(a) g'(a)$. $\square$

::: mathlib
`HasDerivAt.mul` · `Mathlib.Analysis.Calculus.Deriv.Mul`

`HasDerivAt (c * d) (c' * d x + c x * d') x`. The values may lie in a normed algebra, for example matrices, and the order of the factors is kept. The sum rule is `HasDerivAt.add`. The `deriv` forms, such as `deriv_mul`, need `DifferentiableAt` hypotheses because of the junk value.

<?decl HasDerivAt.mul?>
:::

**Theorem (Chain rule).** Let $g$ be differentiable at $a$ and $f$ differentiable at $b = g(a)$. Then $(f \circ g)'(a) = f'(g(a))\, g'(a)$.

*Proof.* Take $\psi$ for $g$ at $a$ and $\varphi$ for $f$ at $b$ from the criterion. Since $g$ is continuous at $a$, $g(x)$ is near $b$ for $x$ near $a$, and
$$f(g(x)) - f(g(a)) = \varphi(g(x))\,(g(x) - g(a)) = \varphi(g(x))\, \psi(x)\, (x - a).$$
The function $\varphi \circ g$ is continuous at $a$, as a composition of continuous functions (Chapter 2). So $\chi = (\varphi \circ g)\psi$ is continuous at $a$, and $(f \circ g)'(a) = \chi(a) = f'(b) g'(a)$. $\square$

The naive proof divides by $g(x) - g(a)$, which can be $0$ for $x$ arbitrarily close to $a$, for example for $g(x) = x^2 \sin(1/x)$ at $0$. The criterion avoids this division.

::: mathlib
`HasDerivAt.comp` · `Mathlib.Analysis.Calculus.Deriv.Comp`

From `HasDerivAt h₂ h₂' (h x)` and `HasDerivAt h h' x` it gives `HasDerivAt (h₂ ∘ h) (h₂' * h') x`. The point `x` is the first explicit argument: `hf.comp x hg`. The `deriv` form is `deriv_comp`.

<?decl HasDerivAt.comp?>
:::

**Theorem (Quotient rule).** If $f, g$ are differentiable at $a$ and $g(a) \neq 0$, then
$$\Big(\frac{f}{g}\Big)'(a) = \frac{f'(a) g(a) - f(a) g'(a)}{g(a)^2}.$$

*Proof.* For $b \neq 0$ and $y \neq 0$, $\frac1y - \frac1b = -\frac{1}{yb}(y - b)$, and $y \mapsto -\frac{1}{yb}$ is continuous at $b$. So $u(y) = 1/y$ has $u'(b) = -1/b^2$. Since $g$ is continuous at $a$ with $g(a) \neq 0$, $g \neq 0$ near $a$. The chain rule gives $(1/g)'(a) = -g'(a)/g(a)^2$. The product rule for $f \cdot (1/g)$ gives $\frac{f'(a)}{g(a)} - \frac{f(a) g'(a)}{g(a)^2}$, which is the claim. $\square$

::: mathlib
`HasDerivAt.div` · `Mathlib.Analysis.Calculus.Deriv.Inv`

`HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x` under the hypothesis `d x ≠ 0`. Without the hypothesis the statement is false.

<?decl HasDerivAt.div?>
:::

**Theorem (Power rule).** For $n \ge 0$, $(x^n)' = n x^{n-1}$ on $\mathbb{R}$. For $n < 0$ the formula holds at each $x \neq 0$. So each polynomial is differentiable, with the formal derivative as its derivative, and each rational function is differentiable where its denominator is not $0$.

*Proof.* Induction on $n \ge 0$. The constant $1$ has each slope $0$. If the claim holds for $n$, the product rule for $x \cdot x^n$ gives $x^n + x \cdot n x^{n-1} = (n+1)x^n$. For $n = -m < 0$ the quotient rule for $1/x^m$ gives $-m x^{m-1}/x^{2m} = n x^{n-1}$. Polynomials and rational functions follow by the sum and quotient rules. $\square$

::: mathlib
`hasDerivAt_pow` · `Mathlib.Analysis.Calculus.Deriv.Pow`

`HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x` for `n : ℕ`. For `n = 0` the truncated exponent `n - 1` is `0`, and the value is `0`. For integer exponents use `hasDerivAt_zpow`, and for polynomials `Polynomial.hasDerivAt`.

<?decl hasDerivAt_pow?>
:::

**Theorem (Derivative of an inverse function).** Let $g$ be continuous at $a$, $f(g(y)) = y$ for $y$ near $a$, and $f$ differentiable at $b = g(a)$ with $f'(b) \neq 0$. Then $g'(a) = 1/f'(b)$.

*Proof.* Take $\varphi$ for $f$ at $b$ from the criterion. For $y$ near $a$, $g(y)$ is near $b$, and with $z = g(y)$:
$$y - a = f(g(y)) - f(g(a)) = \varphi(g(y))\,(g(y) - g(a)).$$
The function $\varphi \circ g$ is continuous at $a$ with value $f'(b) \neq 0$, so it is nonzero near $a$, and $g(y) - g(a) = \frac{1}{\varphi(g(y))}(y - a)$. The factor is continuous at $a$ with value $1/f'(b)$. The criterion gives the claim. $\square$

The hypothesis $f'(b) \neq 0$ is needed: the inverse $y^{1/3}$ of $x^3$ has the slope $h^{-2/3} \to \infty$ at $0$.

::: mathlib
`HasDerivAt.of_local_left_inverse` · `Mathlib.Analysis.Calculus.Deriv.Inverse`

The theorem with the hypotheses `ContinuousAt g a`, `HasDerivAt f f' (g a)`, `f' ≠ 0` and `∀ᶠ y in 𝓝 a, f (g y) = y`, and the conclusion `HasDerivAt g f'⁻¹ a`. The derivatives of `Real.sqrt`, `Real.log` and `Real.arcsin` come from this lemma.

<?decl HasDerivAt.of_local_left_inverse?>
:::

### Examples

**Example (A quotient).** Let $f(x) = \frac{x^2 + 1}{x - 1}$. The quotient rule gives $f'(x) = \frac{2x(x - 1) - (x^2 + 1)}{(x - 1)^2} = \frac{x^2 - 2x - 1}{(x - 1)^2}$, so $f'(3) = \frac{2}{4} = \frac12$. Check from the definition: $f(3) = 5$ and
$$\frac{f(3 + h) - 5}{h} = \frac{10 + 6h + h^2 - 10 - 5h}{h(2 + h)} = \frac{1 + h}{2 + h} \to \frac12.$$

**Counterexample (The absolute value).** For $f(x) = |x|$ the slope at $0$ is $1$ for $h > 0$ and $-1$ for $h < 0$. The right derivative is $1$, the left derivative is $-1$, and $f$ is not differentiable at $0$, although it is continuous there. So the converse of "differentiable implies continuous" fails.

::: mathlib
`deriv_abs` · `Mathlib.Analysis.Calculus.Deriv.Abs`

`deriv (fun x => |x|) x = SignType.sign x` for every `x`. At `0` both sides are `0`, the left side by the junk value.

<?decl deriv_abs?>
:::

**Counterexample (A derivative that is not continuous).** Let $f(x) = x^2 \sin(1/x)$ for $x \neq 0$ and $f(0) = 0$, with $\sin$ and $\cos$ from Chapter 6. The slope at $0$ is $h \sin(1/h)$, with $|h \sin(1/h)| \le |h|$, so $f'(0) = 0$. For $x \neq 0$,
$$f'(x) = 2x \sin(1/x) - \cos(1/x).$$
On $x_n = \frac{1}{2\pi n}$, $f'(x_n) \to -1$, and on $y_n = \frac{1}{(2n+1)\pi}$, $f'(y_n) \to 1$. So $f$ is differentiable on $\mathbb{R}$, but $f'$ has no limit at $0$.

### The library around it

The files `Mathlib.Analysis.Calculus.Deriv.*` state each rule for `HasDerivAt`, `HasDerivWithinAt` and `deriv`, with regular names: `HasDerivAt.add`, `HasDerivWithinAt.add`, `deriv_add`. A computed derivative often needs `convert ... using 1; ring`, because the rules produce `↑3 * x ^ (3 - 1) * 1 + 0` and not `3 * x ^ 2`. The tactic `fun_prop` proves `DifferentiableAt ℝ f x` for expressions built from differentiable pieces.

Common errors of a learner:

- Reading `deriv f x = 0` as "f has a critical point at x". It also holds where `f` is not differentiable.
- Forgetting the side condition `d x ≠ 0` of the quotient rule. `simp` leaves it as a goal.
- Computing $f'(a)$ as $\lim_{x \to a} f'(x)$. The function $x^2 \sin(1/x)$ shows that the second limit may not exist.
- Putting the point in the wrong place in `HasDerivAt.comp`: the hypothesis on the outer function is at `h x`, not at `x`.

### Exercises

1. (A) Compute from the definition the derivative of $1/x^2$ at $2$. Check it with the power rule.
2. (A) Let $f(x) = x|x|$. Show that $f'(x) = 2|x|$ on $\mathbb{R}$. Hint: at $0$ use the definition.
3. (B) Let $f$ be differentiable at $a$. Show that $\frac{f(a + h) - f(a - h)}{2h} \to f'(a)$. Give a function for which this limit exists at $0$ but $f'(0)$ does not.
4. (B) Let $f(x) = x + x^3$. Show that $f$ is a bijection of $\mathbb{R}$ and compute $(f^{-1})'(2)$. Hint: $f(1) = 2$.
5. (C) Prove the chain rule from the linear approximation form, without the criterion. Hint: write $f(y) = f(b) + f'(b)(y - b) + \varepsilon(y)(y - b)$ with $\varepsilon$ continuous at $b$ and $\varepsilon(b) = 0$.

### Notes and history

Cauchy (1823) defined the derivative as the limit of the difference quotient. The criterion with $\varphi$ is due to Carathéodory (1950). In Mathlib the file of the one-variable derivative has the authors Gabriel Ebner and Sébastien Gouëzel. The pair of a relation `HasDerivAt` and a total function `deriv` with a junk value is the pattern of the library.

### Reference

<?reference?>
