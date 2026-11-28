---
title: The hyperbolic functions and their inverses
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
  - Mathlib.Analysis.SpecialFunctions.Arsinh
  - Mathlib.Analysis.SpecialFunctions.Arcosh
  - Mathlib.Analysis.SpecialFunctions.Artanh
explains:
  E2: [Real.cosh_le_cosh, Real.sinh_sub_id_strictMono, Real.sinh_arsinh, Real.hasDerivAt_arsinh, Real.cosh_arcosh, Real.artanh_eq_half_log, Real.log_two_eq_six_mul_artanh_add]
  E1: auto
families: []
requires: [V02, V13, V15.C03, V15.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The hyperbolic functions and their inverses

### Overview

The hyperbolic sine and cosine are the even and the odd parts of the exponential:
$$\sinh x = \frac{e^x - e^{-x}}{2}, \qquad \cosh x = \frac{e^x + e^{-x}}{2}, \qquad \tanh x = \frac{\sinh x}{\cosh x}.$$
Mathlib defines `Real.sinh`, `Real.cosh` and `Real.tanh` next to the sine and the cosine, as the real parts of the complex functions `Complex.sinh` and `Complex.cosh`. The algebraic identities come with the definitions: `Real.sinh_eq` and `Real.cosh_eq` are the formulas above, `Real.cosh_sq` says $\cosh^2 x = \sinh^2 x + 1$, `Real.cosh_add_sinh` says $\cosh x + \sinh x = e^x$, and `Real.abs_tanh_lt_one` says $\lvert\tanh x\rvert < 1$.

This section treats the analysis of these functions and their inverses. The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp` computes the derivatives of $\sinh$ and $\cosh$, and it proves the order properties that need the mean value theorem: $\sinh$ is strictly increasing, and $\cosh$ is strictly increasing on $[0, \infty)$. The modules `Mathlib.Analysis.SpecialFunctions.Arsinh`, `Mathlib.Analysis.SpecialFunctions.Arcosh` and `Mathlib.Analysis.SpecialFunctions.Artanh` define the three inverse functions by explicit formulas with the logarithm of Chapter 5 and the square root of Chapter 2:
$$\operatorname{arsinh} x = \log\bigl(x + \sqrt{1 + x^2}\bigr), \quad \operatorname{arcosh} x = \log\bigl(x + \sqrt{x^2 - 1}\bigr), \quad \operatorname{artanh} x = \log\sqrt{\tfrac{1 + x}{1 - x}}.$$
The three definitions are total, as the logarithm is. Outside the natural domains they give junk values, and the hypotheses of the lemmas exclude these values.

### The library around it

#### Derivatives of sinh and cosh

The derivatives follow from $\exp' = \exp$ and the chain rule. The file states them first over $\mathbb{C}$ and then over $\mathbb{R}$, with the same names in the two namespaces:

| Lean name | Statement |
|---|---|
| `Real.hasDerivAt_sinh` | $\sinh'(x) = \cosh x$ |
| `Real.hasDerivAt_cosh` | $\cosh'(x) = \sinh x$ |
| `Real.deriv_sinh` | `deriv sinh = cosh` |
| `Real.deriv_cosh` | `deriv cosh = sinh` |
| `Real.contDiff_sinh` | $\sinh$ is $C^n$ for every $n$ |
| `Real.analyticAt_sinh` | $\sinh$ is analytic at every point |
| `Real.logDeriv_cosh` | the logarithmic derivative of $\cosh$ is $\tanh$ |
| `Real.isEquivalent_sinh` | $\sinh x \sim x$ as $x \to 0$ |

The complex versions are `Complex.hasDerivAt_sinh`, `Complex.contDiff_cosh` and so on. The strict derivatives `Real.hasStrictDerivAt_sinh` and `Real.hasStrictDerivAt_cosh` feed the inverse function theorem below.

For a composite $x \mapsto \sinh(f(x))$ the file has the chain rule lemmas in the dot notation of Chapter 3: `HasDerivAt.sinh`, `HasDerivWithinAt.sinh`, `DifferentiableAt.sinh`, `Differentiable.sinh`, `ContDiff.sinh` and the versions for the Fréchet derivative, `HasFDerivAt.sinh` and `fderiv_sinh`. The complex functions use a prefix c: `HasDerivAt.csinh`, `HasDerivAt.ccosh`, `Differentiable.ccosh`. This is the same naming pattern as `HasDerivAt.exp` and `HasDerivAt.cexp` of Chapter 5. With these lemmas the tactic `fun_prop` proves the differentiability of expressions in $\sinh$ and $\cosh$.

The iterated derivatives repeat with period $2$: `Real.iteratedDeriv_even_sinh` says that the derivative of order $2n$ of $\sinh$ is $\sinh$, and `Real.iteratedDeriv_odd_sinh` says that the derivative of order $2n + 1$ is $\cosh$. The lemmas `Real.iteratedDeriv_even_cosh` and `Real.iteratedDeriv_odd_cosh` do the same for $\cosh$, and `Real.iteratedDerivWithin_sinh_Icc` lets the Taylor theorem of Chapter 4, which works within an interval, use them.

#### Order properties

**Theorem.** The function $\sinh$ is strictly increasing on $\mathbb{R}$, and $\cosh$ is strictly increasing on $[0, \infty)$. So $\cosh x \le \cosh y$ if and only if $\lvert x\rvert \le \lvert y\rvert$.

*Proof.* The derivative of $\sinh$ is $\cosh$, and $\cosh x > 0$. By the mean value theorem, $\sinh$ is strictly increasing. Then $\sinh x > \sinh 0 = 0$ for $x > 0$. The derivative of $\cosh$ is $\sinh$, which is positive on $(0, \infty)$, so $\cosh$ is strictly increasing on $[0, \infty)$. Since $\cosh$ is even, $\cosh x = \cosh\lvert x\rvert$, and the last claim follows from the monotonicity on $[0, \infty)$. $\square$

In Lean these are `Real.sinh_strictMono`, `Real.cosh_strictMonoOn` and `Real.cosh_le_cosh`. The usual corollaries are simp lemmas of iff form: `Real.sinh_inj`, `Real.sinh_le_sinh`, `Real.sinh_lt_sinh`, `Real.sinh_pos_iff`, `Real.sinh_nonneg_iff`, `Real.sinh_eq_zero`, `Real.cosh_lt_cosh`, `Real.one_le_cosh` and `Real.one_lt_cosh` ($1 < \cosh x \iff x \ne 0$). The lemma `Real.abs_sinh` says $\lvert\sinh x\rvert = \sinh\lvert x\rvert$.

**Theorem.** The function $x \mapsto \sinh x - x$ is strictly increasing. So $x \le \sinh x$ if and only if $x \ge 0$.

*Proof.* Its derivative is $\cosh x - 1$, which is $\ge 0$ and is zero only at $x = 0$. A function with a nonnegative derivative that vanishes at a single point is strictly increasing. At $x = 0$ the function is $0$. $\square$

This is `Real.sinh_sub_id_strictMono`, with the consequences `Real.self_le_sinh_iff`, `Real.self_lt_sinh_iff`, `Real.sinh_le_self_iff` and `Real.sinh_lt_self_iff`. The module also registers an extension of the `positivity` tactic, `Mathlib.Meta.Positivity.evalSinh`: it proves $0 < \sinh x$, $0 \le \sinh x$ or $\sinh x \ne 0$ from the same fact about $x$.

#### The inverse hyperbolic sine

The function $\sinh$ is a bijection of $\mathbb{R}$, and `Real.arsinh` is its inverse.

**Theorem.** For every real $x$, $\sinh(\operatorname{arsinh} x) = x$.

*Proof.* Let $u = x + \sqrt{1 + x^2}$. Then $u > 0$, because $\sqrt{1 + x^2} > \lvert x\rvert$. The product $(x + \sqrt{1 + x^2})(\sqrt{1 + x^2} - x)$ is $1 + x^2 - x^2 = 1$, so $u^{-1} = \sqrt{1 + x^2} - x$. Since $e^{\operatorname{arsinh} x} = u$, the definition of $\sinh$ gives $\sinh(\operatorname{arsinh} x) = (u - u^{-1})/2 = x$. $\square$

This is `Real.sinh_arsinh`. The first step is `Real.exp_arsinh`. The other direction, `Real.arsinh_sinh`, follows because $\sinh$ is injective. From the two identities the library builds three bundled forms of the bijection: `Real.sinhEquiv` as an equivalence, `Real.sinhOrderIso` as an order isomorphism, and `Real.sinhHomeomorph` as a homeomorphism. Their simp lemmas, such as `Real.sinhEquiv_symm_apply`, unfold the inverse to `Real.arsinh`. The order isomorphism gives the order lemmas: `Real.arsinh_strictMono`, `Real.arsinh_le_arsinh`, `Real.arsinh_lt_arsinh`, `Real.arsinh_pos_iff`, `Real.arsinh_nonneg_iff` and `Real.arsinh_eq_zero_iff`. The function is odd (`Real.arsinh_neg`) and `Real.cosh_arsinh` says $\cosh(\operatorname{arsinh} x) = \sqrt{1 + x^2}$.

**Theorem.** The derivative of $\operatorname{arsinh}$ at $x$ is $1/\sqrt{1 + x^2}$.

*Proof.* By the inverse function theorem of Chapter 3, the derivative of the inverse at $x$ is $1/\sinh'(\operatorname{arsinh} x) = 1/\cosh(\operatorname{arsinh} x)$. By `Real.cosh_arsinh` this is $1/\sqrt{1 + x^2}$. $\square$

This is `Real.hasDerivAt_arsinh`, with the strict form `Real.hasStrictDerivAt_arsinh`. The module then gives $C^\infty$ and analyticity, `Real.contDiff_arsinh` and `Real.analyticAt_arsinh`, and the full family of composite lemmas: `Filter.Tendsto.arsinh`, `Continuous.arsinh`, `HasDerivAt.arsinh`, `DifferentiableOn.arsinh`, `ContDiff.arsinh` and the others.

#### The inverse hyperbolic cosine

The function $\cosh$ is not injective on $\mathbb{R}$, so its inverse lives on a domain: $\cosh$ is a bijection from $[0, \infty)$ onto $[1, \infty)$. The inverse is `Real.arcosh`.

**Theorem.** For $x \ge 1$, $\cosh(\operatorname{arcosh} x) = x$. For $x \ge 0$, $\operatorname{arcosh}(\cosh x) = x$.

*Proof.* For $x \ge 1$, let $u = x + \sqrt{x^2 - 1} \ge 1$. As for $\operatorname{arsinh}$, $u^{-1} = x - \sqrt{x^2 - 1}$ (the lemma `Real.add_sqrt_self_sq_sub_one_inv`). So $\cosh(\log u) = (u + u^{-1})/2 = x$. For the second claim, $\cosh x \ge 1$, so $\cosh(\operatorname{arcosh}(\cosh x)) = \cosh x$. Both $x$ and $\operatorname{arcosh}(\cosh x)$ are $\ge 0$, and $\cosh$ is injective on $[0, \infty)$. $\square$

These are `Real.cosh_arcosh` and `Real.arcosh_cosh`. The library bundles the pair as `Real.coshPartialEquiv`, a partial equivalence (Volume 1) from $[0, \infty)$ to $[1, \infty)$, and reads the set statements from it: `Real.cosh_bijOn`, `Real.cosh_injOn`, `Real.cosh_surjOn`, `Real.arcosh_bijOn`. On the open sets $(0, \infty)$ and $(1, \infty)$ it is the open partial homeomorphism `Real.coshOpenPartialHomeomorph`. The derivative comes from it: `Real.hasDerivAt_arcosh` says that $\operatorname{arcosh}'(x) = 1/\sqrt{x^2 - 1}$ for $x > 1$. The derivative is infinite at $x = 1$, and the lemma excludes this point. `Real.continuousOn_arcosh` gives the continuity on $[1, \infty)$, and `Real.sinh_arcosh` says $\sinh(\operatorname{arcosh} x) = \sqrt{x^2 - 1}$ for $x \ge 1$.

#### The inverse hyperbolic tangent

The function $\tanh$ is a bijection from $\mathbb{R}$ onto $(-1, 1)$ (`Real.tanh_bijOn`, `Real.tanh_injective`), and `Real.artanh` is its inverse. The pair is bundled as `Real.tanhPartialEquiv`. The identities are `Real.tanh_artanh` for $x \in (-1, 1)$ and `Real.artanh_tanh` for every $x$. The function is strictly increasing on $(-1, 1)$ (`Real.strictMonoOn_artanh`), as the composite of the logarithm, the square root and the increasing map $x \mapsto (1 + x)/(1 - x)$ (`Real.strictMonoOn_one_add_div_one_sub`).

**Theorem.** For $x \in [-1, 1]$, $\operatorname{artanh} x = \frac{1}{2}\log\frac{1 + x}{1 - x}$.

*Proof.* The quotient $(1 + x)/(1 - x)$ is $\ge 0$ on $[-1, 1]$; at $x = 1$ it is $2/0 = 0$ in Mathlib. For $t \ge 0$, $\log\sqrt{t} = \frac{1}{2}\log t$ (the lemma `Real.log_sqrt`). $\square$

This is `Real.artanh_eq_half_log`. Read backwards, it expresses every logarithm by $\operatorname{artanh}$: `Real.log_eq_two_mul_artanh` says $\log x = 2\operatorname{artanh}\frac{x - 1}{x + 1}$ for $x \ge 0$. The point of this form is speed. The series $\operatorname{artanh} t = t + t^3/3 + t^5/5 + \cdots$ converges fast for small $t$.

**Theorem.** $\log 2 = 6\operatorname{artanh}\frac{1}{17} + 4\operatorname{artanh}\frac{1}{19} + 4\operatorname{artanh}\frac{1}{31}$.

*Proof.* The numbers $t = 1/17, 1/19, 1/31$ give $(1 + t)/(1 - t) = 9/8, 10/9, 16/15$. So the right side is $3\log\frac{9}{8} + 2\log\frac{10}{9} + 2\log\frac{16}{15}$. This is $\log$ of $\frac{9^3}{8^3}\cdot\frac{10^2}{9^2}\cdot\frac{16^2}{15^2} = \frac{729 \cdot 100 \cdot 256}{512 \cdot 81 \cdot 225} = 2$. $\square$

This is `Real.log_two_eq_six_mul_artanh_add`. The module also has the values of the other hyperbolic functions at $\operatorname{artanh} x$: `Real.exp_artanh`, `Real.sinh_artanh` and `Real.cosh_artanh`. It has no derivative lemma for $\operatorname{artanh}$. The derivative $1/(1 - x^2)$ follows from the formula with the logarithm, as Exercise 4 shows.

#### Common errors

1. Using `Real.arcosh` or `Real.artanh` outside the domain. For $0 < x < 1$ the square root in the definition of $\operatorname{arcosh}$ is $\sqrt{\text{negative}} = 0$, so `Real.arcosh x = Real.log x`, a negative number. For $\lvert x\rvert \ge 1$, `Real.artanh x = 0` (`Real.artanh_eq_zero_iff`). Most lemmas carry the hypothesis $1 \le x$ or $x \in (-1, 1)$ for this reason.
2. Searching for a lemma named arcosh_one. The lemma $\operatorname{arcosh} 1 = 0$ has the name `Real.arcosh_zero`, after the value and not the argument.
3. Confusing the real and the complex chain rules. `HasDerivAt.sinh` is for a real function $f$ and `Real.sinh`; `HasDerivAt.csinh` is for a complex function and `Complex.sinh`.

### Exercises

1. (A) Compute $\operatorname{arsinh} 0$, $\operatorname{arcosh} 1$ and $\operatorname{artanh}(1/2)$ in closed form, and give the Mathlib values of $\operatorname{arcosh}(1/2)$ and $\operatorname{artanh} 2$.
2. (A) Show that $\operatorname{arsinh}$ is odd, from `Real.sinh_injective` and the oddness of $\sinh$.
3. (A) Find the derivative of $x \mapsto \sinh(x^2)\cosh x$ and name the Mathlib lemmas that prove it.
4. (B) Show that $\operatorname{artanh}$ has derivative $1/(1 - x^2)$ on $(-1, 1)$. Hint: `Real.artanh_eq_half_log` and the derivative of $\log$.
5. (B) Show that $\cosh x \ge 1 + x^2/2$ for all real $x$. Hint: the function $\cosh x - 1 - x^2/2$ has the derivative $\sinh x - x$.
6. (C) Prove that $\operatorname{arsinh} x - \log(2x) \to 0$ as $x \to \infty$, and deduce that $\operatorname{arsinh} x \sim \log x$.

### Reference

<?reference?>
