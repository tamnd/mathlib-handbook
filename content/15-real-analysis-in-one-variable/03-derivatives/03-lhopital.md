---
title: The rule of l'Hôpital
kind: theory
modules:
  - Mathlib.Analysis.Calculus.LHopital
explains:
  E3: [HasDerivAt.lhopital_zero_right_on_Ioo, HasDerivAt.lhopital_zero_nhds, HasDerivAt.lhopital_zero_atTop]
  E2: [HasDerivAt.lhopital_zero_nhdsNE, deriv.lhopital_zero_nhds]
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

## The rule of l'Hôpital

### Overview

A limit $\lim_{x \to a} \frac{f(x)}{g(x)}$ with $f(x) \to 0$ and $g(x) \to 0$ is an indeterminate form $0/0$: the quotient rule for limits of Chapter 2 does not apply. The rule of l'Hôpital says that, under hypotheses on the derivatives, the limit of $f/g$ is the limit of $f'/g'$ when the second limit exists. The proof is a direct consequence of the mean value theorem of Cauchy from Section 2. The section proves the rule at a point and at $+\infty$, and shows by counterexamples that the hypotheses are needed. Chapter 4 gives the same limits by Taylor expansions, and Chapter 7 organizes them with asymptotic notation.

### Definitions

**Definition (Indeterminate form $0/0$).** Let $a \in \mathbb{R}$ or $a = \pm\infty$, and let $f, g$ be defined near $a$, except perhaps at $a$. The quotient $f/g$ has the *indeterminate form* $0/0$ at $a$ if $f(x) \to 0$ and $g(x) \to 0$ as $x \to a$.

The limits of $f$ and $g$ alone do not decide the limit of $f/g$. With $g(x) = x$ at $0$, the choices $f(x) = cx$, $x^2$, $x^{1/3}$ and $x \sin(1/x)$ give the limits $c$, $0$, $+\infty$ and no limit. In this section a limit $L$ may be a real number or $\pm\infty$.

::: mathlib
`nhdsWithin` · `Mathlib.Topology.Defs.Filter`

The limits of this section are `Filter.Tendsto` statements for the filters of Volume 13: `𝓝[>] a`, `𝓝[<] a`, `𝓝[≠] a`, `atTop` and `atBot`. A finite limit $L$ is the filter `𝓝 L`, and $\pm\infty$ are `atTop` and `atBot`. The rule in Mathlib allows any filter `l` as the limit of `f'/g'`, so the finite and the infinite cases are one theorem.

<?decl nhdsWithin?>
:::

### Theorems and proofs

**Theorem (L'Hôpital, right limit at a point).** Let $a < b$, let $f, g$ be differentiable on $(a, b)$ with $g' \neq 0$ there, let $f(x) \to 0$ and $g(x) \to 0$ as $x \to a^+$, and let $\frac{f'(x)}{g'(x)} \to L$ as $x \to a^+$. Then $g \neq 0$ on $(a, b)$ and $\frac{f(x)}{g(x)} \to L$ as $x \to a^+$.

*Proof.* Step 1. Let $F = f$ and $G = g$ on $(a, b)$, and $F(a) = G(a) = 0$. Then $F$ and $G$ are continuous on $[a, b)$: at $a$ by the hypothesis on the limits, and on $(a, b)$ because they are differentiable there.

Step 2. Let $x \in (a, b)$. If $g(x) = 0$, then $G(a) = G(x)$, and Rolle's theorem on $[a, x]$ gives a zero of $g'$ in $(a, x)$, which is excluded. So $g(x) \neq 0$.

Step 3. The mean value theorem of Cauchy for $F$ and $G$ on $[a, x]$ gives $c_x \in (a, x)$ with $g(x) f'(c_x) = f(x) g'(c_x)$. Since $g(x) \neq 0$ and $g'(c_x) \neq 0$,
$$\frac{f(x)}{g(x)} = \frac{f'(c_x)}{g'(c_x)}, \qquad a < c_x < x. \tag{1}$$

Step 4. Let $L \in \mathbb{R}$ and $\varepsilon > 0$. Choose $\delta \in (0, b - a]$ with $\big|\frac{f'(t)}{g'(t)} - L\big| < \varepsilon$ for $t \in (a, a + \delta)$. For $x \in (a, a + \delta)$, $c_x \in (a, a + \delta)$, so by (1), $\big|\frac{f(x)}{g(x)} - L\big| < \varepsilon$. For $L = +\infty$ replace the condition by "$> M$" for an arbitrary $M$, and for $L = -\infty$ by "$< M$". $\square$

The point $c_x$ depends on $x$ in an uncontrolled way. The proof uses only $a < c_x < x$. This is why the rule needs the limit of $f'/g'$ over all points near $a$, not along a special sequence.

::: mathlib
`HasDerivAt.lhopital_zero_right_on_Ioo` · `Mathlib.Analysis.Calculus.LHopital`

The theorem as stated, with `HasDerivAt f (f' x) x`, `HasDerivAt g (g' x) x` and `g' x ≠ 0` on `Ioo a b`, the limits of `f` and `g` along `𝓝[>] a` equal to `0`, and `Tendsto (fun x => f' x / g' x) (𝓝[>] a) l` for any filter `l`. The proof follows the steps above, with `exists_hasDerivAt_eq_zero'` and `exists_ratio_hasDerivAt_eq_ratio_slope'`, forms of Rolle and Cauchy with limits at the end points in place of an extension. The other forms in the file come from this one by composition with $x \mapsto -x$ and $x \mapsto 1/x$.

<?decl HasDerivAt.lhopital_zero_right_on_Ioo?>
:::

**Corollary (Left and two-sided limits).** The theorem holds for $x \to a^-$. If the hypotheses hold on both sides of $a$ and $f'/g' \to L$ as $x \to a$ with $x \neq a$, then $f/g \to L$ as $x \to a$ with $x \neq a$.

*Proof.* For the left limit apply the theorem to $f(-x)$ and $g(-x)$ at $-a$. By the chain rule their derivatives are $-f'(-x)$ and $-g'(-x) \neq 0$, and the quotient is $\frac{f'(-x)}{g'(-x)}$. The two-sided limit exists when both one-sided limits exist and are equal (Chapter 2). $\square$

::: mathlib
`HasDerivAt.lhopital_zero_nhds` · `Mathlib.Analysis.Calculus.LHopital`

The two-sided form. Its hypotheses are eventual along `𝓝 a`, so they include the point `a`: `f` and `g` must be differentiable at `a`. The conclusion is along `𝓝[≠] a`. The form `HasDerivAt.lhopital_zero_nhdsNE` puts every hypothesis along `𝓝[≠] a`.

<?decl HasDerivAt.lhopital_zero_nhds?>
:::

::: mathlib
`HasDerivAt.lhopital_zero_nhdsNE` · `Mathlib.Analysis.Calculus.LHopital`

The two-sided form with no assumption at `a` itself, the closest to the corollary.

<?decl HasDerivAt.lhopital_zero_nhdsNE?>
:::

**Theorem (L'Hôpital at infinity).** Let $f, g$ be differentiable on $(R, \infty)$, $R > 0$, with $g' \neq 0$ there, $f, g \to 0$ as $x \to +\infty$, and $f'/g' \to L$ as $x \to +\infty$. Then $f/g \to L$ as $x \to +\infty$.

*Proof.* Let $F(t) = f(1/t)$ and $G(t) = g(1/t)$ on $(0, 1/R)$. Since $1/t \to +\infty$ as $t \to 0^+$, $F, G \to 0$ as $t \to 0^+$. By the chain rule $F'(t) = -t^{-2} f'(1/t)$ and $G'(t) = -t^{-2} g'(1/t) \neq 0$, so $\frac{F'(t)}{G'(t)} = \frac{f'(1/t)}{g'(1/t)} \to L$. The theorem at $0^+$ gives $F/G \to L$, and $\frac{f(x)}{g(x)} = \frac{F(1/x)}{G(1/x)} \to L$ because $1/x \to 0^+$. $\square$

::: mathlib
`HasDerivAt.lhopital_zero_atTop` · `Mathlib.Analysis.Calculus.LHopital`

The rule along `atTop` with eventual hypotheses. The proof is the substitution above. The form along `atBot` is `HasDerivAt.lhopital_zero_atBot`.

<?decl HasDerivAt.lhopital_zero_atTop?>
:::

The rule for $\infty/\infty$ is also true (Exercise 6), but Mathlib, at the commit of this book, has only the $0/0$ forms in this file.

### Examples

**Example (A rational function).** For $\lim_{x \to 1} \frac{x^3 - 1}{x^2 - 1}$, both parts tend to $0$, $g'(x) = 2x \neq 0$ near $1$, and $\frac{3x^2}{2x} \to \frac32$. So the limit is $\frac32$. Factoring confirms it: the quotient is $\frac{x^2 + x + 1}{x + 1}$ for $x \neq \pm 1$.

**Example (The rule twice).** For $\lim_{x \to 0} \frac{1 - \cos x}{x^2}$, with $\cos' = -\sin$ and $\sin' = \cos$ from Chapter 6, the quotient of derivatives is $\frac{\sin x}{2x}$, again of the form $0/0$. Its quotient of derivatives $\frac{\cos x}{2}$ tends to $\frac12$, so first $\frac{\sin x}{2x} \to \frac12$, and then $\frac{1 - \cos x}{x^2} \to \frac12$. The rule applies to the outer quotient only after the inner limit is known to exist.

**Example (At infinity).** For $x \log(1 + 1/x)$ as $x \to +\infty$, with $\log' = 1/y$ from Chapter 5, take $f(x) = \log(1 + 1/x)$ and $g(x) = 1/x$. Then $\frac{f'(x)}{g'(x)} = \frac{1}{1 + 1/x} \to 1$, so the limit is $1$, and $(1 + 1/x)^x \to e$ by the continuity of $\exp$.

**Counterexample (The form must be $0/0$).** For $\frac{x + 1}{x + 2}$ at $0$ the limit is $\frac12$, but $f'/g' = 1$. The hypothesis $f, g \to 0$ fails.

**Counterexample (The converse fails).** Let $f(x) = x^2 \sin(1/x)$, $f(0) = 0$, and $g(x) = x$. Then $f/g = x \sin(1/x) \to 0$, but $f'/g' = 2x \sin(1/x) - \cos(1/x)$ has no limit at $0$. The rule gives no information in this case.

**Counterexample (The hypothesis $g' \neq 0$, Stolz).** As $x \to +\infty$ let $f(x) = x + \sin x \cos x$ and $g(x) = e^{\sin x} f(x)$, a form $\infty/\infty$. Then $f'(x) = 2\cos^2 x$ and $g'(x) = e^{\sin x}\cos x\,(x + \sin x \cos x + 2\cos x)$. Where $\cos x \neq 0$,
$$\Big|\frac{f'(x)}{g'(x)}\Big| = \frac{2|\cos x|\, e^{-\sin x}}{|x + \sin x \cos x + 2\cos x|} \le \frac{2e}{x - 3} \to 0,$$
but $f/g = e^{-\sin x}$ has no limit. The rule fails because $g'$ vanishes at $\frac{\pi}{2} + k\pi$ for arbitrarily large $x$, and the cancellation of $\cos x$ hides these zeros.

### The library around it

Each form of the rule exists in the namespace `HasDerivAt`, with the derivatives as functions `f'` and `g'`, and in the namespace `deriv`. The suffixes give the approach: `right_on_Ioo`, `left_on_Ioo`, `nhdsGT`, `nhdsLT`, `nhdsNE`, `nhds`, `atTop`, `atBot`, and `nhdsWithin_convex`.

::: mathlib
`deriv.lhopital_zero_nhds` · `Mathlib.Analysis.Calculus.LHopital`

The two-sided `deriv` form. It needs `DifferentiableAt ℝ f x` near `a` but not the same for `g`: the hypothesis `deriv g x ≠ 0` already implies that `g` is differentiable at `x`, because the junk value is `0`.

<?decl deriv.lhopital_zero_nhds?>
:::

In Mathlib many such limits follow faster from the asymptotics of Chapter 7, such as `Real.isLittleO_pow_exp_atTop`, or from a derivative: $\frac{\sin x}{x} \to 1$ is the derivative of $\sin$ at $0$, by `hasDerivAt_iff_tendsto_slope`.

Common errors of a learner:

- Applying the rule to a quotient that is not of the form $0/0$ or $\infty/\infty$.
- Differentiating $f/g$ by the quotient rule in place of forming $f'/g'$.
- Concluding that $f/g$ has no limit because $f'/g'$ has none.
- Forgetting $g' \neq 0$ near the point, as in Stolz's example.
- In Lean, expecting the conclusion of `HasDerivAt.lhopital_zero_nhds` along `𝓝 a`. It is along `𝓝[≠] a`, and `f a / g a = 0 / 0 = 0` is a junk value.

### Exercises

1. (A) Compute $\lim_{x \to 2} \frac{x^4 - 16}{x^3 - 8}$ by the rule, and check it by factoring.
2. (A) Show that $\lim_{x \to 0} \frac{\sin x - x}{x^3} = -\frac16$. Hint: apply the rule three times, checking the hypotheses each time.
3. (A) Compute $\lim_{x \to 0} \frac{\sqrt{1 + x} - 1 - x/2}{x^2}$.
4. (B) Let $f, g$ be differentiable at $a$ with $f(a) = g(a) = 0$ and $g'(a) \neq 0$. Show that $f/g \to f'(a)/g'(a)$, with no hypothesis on $f', g'$ near $a$. Hint: divide by $x - a$.
5. (B) Show that $\frac{e^{-1/x}}{x^n} \to 0$ as $x \to 0^+$ for each $n \ge 1$. Hint: substitute $t = 1/x$.
6. (C) Prove the rule for $\infty/\infty$ at $a^+$ with $L$ finite: if $g' \neq 0$ on $(a, b)$, $|g(x)| \to \infty$ and $f'/g' \to L$, then $f/g \to L$. Hint: fix $y$ with $|f'/g' - L| < \varepsilon$ on $(a, y)$, write $\frac{f(x)}{g(x)} = \frac{f(x) - f(y)}{g(x) - g(y)} \cdot \frac{g(x) - g(y)}{g(x)} + \frac{f(y)}{g(x)}$, apply Cauchy on $[x, y]$, and let $x \to a^+$.

### Notes and history

The rule appeared in 1696 in the first textbook of the calculus, the *Analyse des infiniment petits* of the Marquis de l'Hôpital, but it is due to Johann Bernoulli, his teacher under a paid contract. The proof by the mean value theorem of Cauchy is from Cauchy (1823), and Stolz gave his counterexample in 1879. The Mathlib file `Mathlib.Analysis.Calculus.LHopital` has the author Anatole Dedecker (2020). Its header says that the main proof follows the Wikibooks text on the rule.

### Reference

<?reference?>
