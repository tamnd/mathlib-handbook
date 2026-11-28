---
title: Slopes, logarithmic derivatives and functions of bounded variation
kind: api
modules:
  - Mathlib.Analysis.Calculus.DSlope
  - Mathlib.Analysis.Calculus.LogDeriv
  - Mathlib.Analysis.Calculus.LocalExtr.LineDeriv
  - Mathlib.Analysis.Calculus.AbsolutelyMonotone
  - Mathlib.Analysis.Calculus.Monotone
  - Mathlib.Analysis.BoundedVariation
explains:
  E2: [dslope_same, sub_smul_dslope, continuousAt_dslope_same, logDeriv_mul, logDeriv_comp, logDeriv_prod, IsLocalMin.hasLineDerivAt_eq_zero, eVariation_mul_le, LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_real]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Slopes, logarithmic derivatives and functions of bounded variation

### Overview

This section collects six modules that build new objects from the derivative. The first object is the *slope function* `dslope f a`. It is the difference quotient $\frac{f(b) - f(a)}{b - a}$, extended at $b = a$ by the derivative $f'(a)$. It is continuous at $a$ exactly when $f$ is differentiable at $a$, and it is the tool to divide a function by $x - a$. The second object is the *logarithmic derivative* $f'/f$, which turns products into sums. The third is the directional derivative, with Fermat's theorem in a vector space. The fourth is the class of *absolutely monotone* functions, whose derivatives of all orders are nonnegative.

The last two modules prove a deep theorem of real analysis: a monotone function $f : \mathbb{R} \to \mathbb{R}$ is differentiable at almost every point. The theorem of Lebesgue extends to functions of bounded variation and to Lipschitz functions. The proofs use measure theory, which is the subject of Volume 18. This section states the results, explains the reduction from bounded variation to monotone functions, and gives the elementary bound for the variation of a product.

The section uses the derivative and the junk values of Section 1 and Fermat's theorem of Section 2. The slope `slope f a b` comes from `Mathlib.Analysis.Calculus.Deriv.Slope`, a module of Section 1.

### The library around it

#### The slope function

The module `Mathlib.Analysis.Calculus.DSlope` defines `dslope f a` for $f : \mathbb{K} \to E$ as the function `slope f a` with the value at $a$ replaced by `deriv f a`. In formulas:
$$\mathrm{dslope}\ f\ a\ b = \begin{cases} (b - a)^{-1}\,(f(b) - f(a)) & b \neq a, \\ f'(a) & b = a. \end{cases}$$
The two cases are `dslope_of_ne` and `dslope_same`. The second one is a simp lemma. Away from $a$ the function agrees with the slope on a neighbourhood (`dslope_eventuallyEq_slope_of_ne`), and on the punctured neighbourhood of $a$ (`dslope_eventuallyEq_slope_nhdsNE`).

**Proposition.** For all $a$ and $b$, $(b - a)\cdot \mathrm{dslope}\ f\ a\ b = f(b) - f(a)$.

*Proof.* For $b \neq a$ multiply the slope by $b - a \neq 0$. For $b = a$ both sides are $0$. $\square$

This is `sub_smul_dslope`. It holds without any hypothesis on $f$, so it is the safe way to write $f(b) = f(a) + (b - a)\,g(b)$ with a function $g$. If $f(a) = 0$, it gives $f(b) = (b - a)\,\mathrm{dslope}\ f\ a\ b$ (`sub_smul_dslope_of_zero`). The iterated version `pow_sub_smul_iterate_dslope_of_zero` divides by $(b - a)^n$ when the first $n$ iterated slopes vanish at $a$. This is the form of the factorization of an analytic function at a zero of order $n$, and complex analysis uses it for the zeros and the removable singularities of holomorphic functions.

**Proposition.** The function `dslope f a` is continuous at $a$ if and only if $f$ is differentiable at $a$.

*Proof.* The value at $a$ is $f'(a)$ if $f$ is differentiable at $a$, and the slope tends to $f'(a)$ on the punctured neighbourhood. That is the continuity. Conversely, if `dslope f a` is continuous at $a$, the slope has a limit $L$ on the punctured neighbourhood. This limit is the definition of a derivative $f'(a) = L$. $\square$

This is `continuousAt_dslope_same`. At a point $b \neq a$ the slope function has the same regularity as $f$: `continuousAt_dslope_of_ne`, `differentiableAt_dslope_of_ne` and `continuousWithinAt_dslope_of_ne` state the equivalences. On a neighbourhood $s$ of $a$, `continuousOn_dslope` combines the two cases: `dslope f a` is continuous on $s$ if and only if $f$ is continuous on $s$ and differentiable at $a$. The analytic versions `AnalyticAt.dslope` and `AnalyticOnNhd.dslope` say that the slope function of an analytic function is analytic, and `HasFPowerSeriesAt.dslope_fslope` gives its power series: the series of $f$ shifted by one place. The lemma `ContinuousLinearMap.dslope_comp` moves a continuous linear map out of the slope.

#### The logarithmic derivative

The module `Mathlib.Analysis.Calculus.LogDeriv` defines `logDeriv f x` as `deriv f x / f x` (`logDeriv_apply`). For a positive function it is the derivative of $\log f$, but the definition does not use the logarithm, so it works for complex functions too. The junk values follow from those of `deriv` and of the division. The value is $0$ where $f$ is not differentiable (`logDeriv_eq_zero_of_not_differentiableAt`) and where $f(x) = 0$.

The basic values are `logDeriv_id`, $1/x$, `logDeriv_const`, $0$, `logDeriv_pow` and `logDeriv_zpow`, $n/x$, and `logDeriv_inv`, $-1/x$. A nonzero constant factor does not change the logarithmic derivative (`logDeriv_const_mul`, `logDeriv_mul_const`), and neither does a sign (`logDeriv_neg`).

**Proposition.** If $f$ and $g$ are differentiable at $x$ and $f(x) \neq 0 \neq g(x)$, then
$$\frac{(fg)'}{fg}(x) = \frac{f'}{f}(x) + \frac{g'}{g}(x).$$

*Proof.* The product rule gives $(fg)' = f'g + fg'$. Divide by $f(x)g(x) \neq 0$. $\square$

This is `logDeriv_mul`, with the variant `logDeriv_div` for a quotient and `logDeriv_fun_pow` for a power $f^n$, which gives $n f'/f$. An induction on a finite set gives the rule for a product, `logDeriv_prod`:
$$\frac{\left(\prod_{i \in s} f_i\right)'}{\prod_{i \in s} f_i} = \sum_{i \in s} \frac{f_i'}{f_i},$$
under the hypotheses that each $f_i$ is differentiable at $x$ and nonzero at $x$. This identity turns a product of functions into a sum, and it is the first step to study an infinite product through a series.

**Proposition.** If $g$ is differentiable at $x$ and $f$ is differentiable at $g(x)$, then $\frac{(f \circ g)'}{f \circ g}(x) = \frac{f'}{f}(g(x))\, g'(x)$.

*Proof.* The chain rule gives $(f \circ g)'(x) = f'(g(x))\,g'(x)$. Divide by $f(g(x))$. If $f(g(x)) = 0$, both sides are $0$ by the junk value of the division. $\square$

This is `logDeriv_comp`, and `logDeriv_comp_neg` is the case $g(x) = -x$. Two functions with the same logarithmic derivative differ by a constant factor. The lemma `logDeriv_eqOn_iff` states this on an open preconnected set $s$ where $f$ and $g$ are differentiable and nonzero: the logarithmic derivatives agree on $s$ if and only if $f = z\,g$ on $s$ for some $z \neq 0$. The proof uses that $(f/g)' = 0$ on $s$, so $f/g$ is constant on the preconnected set. The congruence lemmas `logDeriv_congr_nhds`, `logDeriv_congr_nhdsNE` and `logDeriv_congr_codiscrete` replace $f$ by a function that agrees with it near a point or outside a discrete set. Finally `AnalyticAt.tendsto_mul_logDeriv_simple_zero` says that near a simple zero $x$ of an analytic $f$, the product $(w - x)\,\frac{f'}{f}(w)$ tends to $1$. In the language of Volume 19, the residue of $f'/f$ at a simple zero is $1$.

#### Fermat's theorem for directional derivatives

The module `Mathlib.Analysis.Calculus.LocalExtr.LineDeriv` proves Fermat's theorem for the directional derivative `lineDeriv ℝ f a b`, the derivative of $t \mapsto f(a + t b)$ at $t = 0$.

**Proposition.** Let $f : E \to \mathbb{R}$ on a topological vector space $E$ have a local minimum at $a$. If $f$ has the directional derivative $f'$ at $a$ in the direction $b$, then $f' = 0$.

*Proof.* The map $t \mapsto a + tb$ is continuous and sends $0$ to $a$. So $t \mapsto f(a + tb)$ has a local minimum at $0$. Its derivative at $0$ is $f'$, and Fermat's theorem of Section 2 gives $f' = 0$. $\square$

This is `IsLocalMin.hasLineDerivAt_eq_zero`. The names follow one pattern: the kind of extremum (`IsLocalMin`, `IsLocalMax`, `IsLocalExtr`, or `IsMinOn`, `IsMaxOn`, `IsExtrOn` on a set, or `IsExtrFilter` along a filter), then the form of the conclusion (`hasLineDerivAt_eq_zero`, `lineDeriv_eq_zero`, `lineDerivWithin_eq_zero`). The versions on a set need the hypothesis that $a + tb \in s$ for all $t$ near $0$. The `lineDeriv_eq_zero` forms need no differentiability, because `lineDeriv` has the junk value $0$.

#### Absolutely monotone functions

The module `Mathlib.Analysis.Calculus.AbsolutelyMonotone` defines `AbsolutelyMonotoneOn f s` for $f : \mathbb{R} \to \mathbb{R}$ and a set $s$. The definition asks for a Taylor series of $f$ up to order $\infty$ on $s$ (the predicate `HasFTaylorSeriesUpToOn` of Chapter 4) whose terms are nonnegative at each point of $s$. In plain words, $f$ is smooth on $s$ and $f^{(n)}(x) \ge 0$ for all $n$ and all $x \in s$. The lemma `AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg` gives this equivalence when $s$ has unique derivatives (`UniqueDiffOn`), for example an interval. The lemma `AbsolutelyMonotoneOn.of_contDiff` is the practical criterion: a function that is smooth on all of $\mathbb{R}$ with $f^{(n)} \ge 0$ on $s$ is absolutely monotone on $s$. For instance $\exp$ is absolutely monotone on $\mathbb{R}$, by `Real.contDiff_exp`, `Real.iter_deriv_exp` and `Real.exp_pos`. The class is closed under sums (`AbsolutelyMonotoneOn.add`) and under multiplication by a constant $c \ge 0$ (`AbsolutelyMonotoneOn.smul`), and each member is smooth (`AbsolutelyMonotoneOn.contDiffOn`).

#### Monotone functions are differentiable almost everywhere

The module `Mathlib.Analysis.Calculus.Monotone` proves the theorem of Lebesgue: a monotone function $f : \mathbb{R} \to \mathbb{R}$ is differentiable at almost every point (`Monotone.ae_differentiableAt`). The proof uses the Stieltjes measure $\mu$ of $f$, which gives the measure $f(y^+) - f(x^-)$ to $[x, y]$. A theorem of the differentiation of measures says that $\mu([x, y]) / (y - x)$ has a limit for almost every $x$, and the limit is the density of $\mu$ with respect to the Lebesgue measure. A comparison of $f(y)$ with the one-sided limits of $f$ then gives the derivative. The lemma `tendsto_apply_add_mul_sq_div_sub` is a technical step of this comparison. The precise forms are `Monotone.ae_hasDerivAt`, which identifies the derivative with the density, `StieltjesFunction.ae_hasDerivAt` for a Stieltjes function, and `MonotoneOn.ae_differentiableWithinAt` for a function monotone on a measurable set.

#### Functions of bounded variation

The module `Mathlib.Analysis.BoundedVariation` treats `BoundedVariationOn f s`. The variation `eVariationOn f s` is the supremum of the sums $\sum_i \|f(x_{i+1}) - f(x_i)\|$ over the finite increasing sequences in $s$, as a value in $[0, \infty]$. The function has bounded variation on $s$ when this value is finite, and `LocallyBoundedVariationOn f s` asks this on each $s \cap [a, b]$. The definitions and the Jordan decomposition are in the topology part of the library.

**Proposition.** If $|f| \le C$ and $|g| \le D$ on $s$, then the variation of $fg$ on $s$ is at most $C\,V(g) + D\,V(f)$.

*Proof.* For two points $x < y$ of $s$,
$$f(y)g(y) - f(x)g(x) = f(y)\,(g(y) - g(x)) + g(x)\,(f(y) - f(x)).$$
So $|f(y)g(y) - f(x)g(x)| \le C\,|g(y) - g(x)| + D\,|f(y) - f(x)|$. Sum over the consecutive points of a finite sequence, and take the supremum. $\square$

This is `eVariation_mul_le`, and it gives `BoundedVariationOn.mul` and `LocallyBoundedVariationOn.mul`. The lemmas `eVariationOn_smul_le`, `BoundedVariationOn.smul` and `BoundedVariationOn.bilinear_comp` are the same argument for a scalar product and for a continuous bilinear map.

**Theorem.** A real function of locally bounded variation on $s$ is differentiable within $s$ at almost every point of $s$.

*Proof sketch.* The Jordan decomposition `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn` writes $f = p - q$ with $p$ and $q$ monotone on $s$. Each of them is differentiable within $s$ almost everywhere on $s$ by the theorem of Lebesgue. The union of two null sets is null. $\square$

This is `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_real`. For a function with values in a finite-dimensional real space $V$, the result follows coordinate by coordinate: `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem` and `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`. A Lipschitz function has locally bounded variation (`LipschitzOnWith.locallyBoundedVariationOn`), so it is differentiable almost everywhere (`LipschitzOnWith.ae_differentiableWithinAt_of_mem_real`, `LipschitzWith.ae_differentiableAt_real`). This is the one-dimensional case of the theorem of Rademacher. The last group of lemmas gives the measure theory of these functions: a function of bounded variation on $\mathbb{R}$ is measurable (`BoundedVariationOn.measurable`), bounded, so in $L^\infty$ (`BoundedVariationOn.memLp_top`), and integrable on each interval inside $s$ (`BoundedVariationOn.intervalIntegrable`).

#### Common errors

1. Writing `slope f a` where the proof needs a value at $a$. The slope has the junk value $0$ at $a$. Use `dslope f a` and `sub_smul_dslope`, which hold at every point.
2. Forgetting the hypotheses $f(x) \neq 0$ and $g(x) \neq 0$ of `logDeriv_mul`. If $f(x) = 0$, then `logDeriv (f * g) x` is $0$, and the sum on the right is in general not $0$.
3. Expecting `Monotone.ae_differentiableAt` to give differentiability at a chosen point. The statement is `∀ᵐ x, DifferentiableAt ℝ f x`, a statement about almost every point. A monotone function can fail to be differentiable on a countable dense set.

### Exercises

1. (A) Compute `dslope (fun x => x ^ 2) 1` as a function: show that its value at $b$ is $b + 1$ for every $b$, also at $b = 1$.
2. (A) Compute the logarithmic derivative of $x^3 (x - 1)^2$ with `logDeriv_mul` and `logDeriv_fun_pow`, at the points where the function is not $0$.
3. (A) Show that $\cosh$ restricted to $[0, \infty)$ is absolutely monotone, and that $\sin$ is not absolutely monotone on any open interval.
4. (B) Let $f$ be differentiable on $\mathbb{R}$ with $f(0) = 0$. Show that $g(x) = f(x)/x$ for $x \neq 0$ and $g(0) = f'(0)$ is continuous at $0$. Name the Mathlib function that is $g$.
5. (B) Show that $f(x) = x \sin(1/x)$ for $x \neq 0$, $f(0) = 0$, does not have bounded variation on $[0, 1]$. Hint: evaluate $f$ at the points $1/(\pi/2 + k\pi)$.
6. (C) Use the theorem of Lebesgue to show that the Cantor function is differentiable at almost every point with the derivative $0$, but is not constant. Explain why this does not contradict the fundamental theorem of calculus.

### Reference

<?reference?>
