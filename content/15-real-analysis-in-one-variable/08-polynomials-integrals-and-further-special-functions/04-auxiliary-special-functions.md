---
title: Auxiliary functions, Bernstein polynomials and the arithmetic-geometric mean
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Sigmoid
  - Mathlib.Analysis.SpecialFunctions.SmoothTransition
  - Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
  - Mathlib.Analysis.SpecialFunctions.JapaneseBracket
  - Mathlib.Analysis.SpecialFunctions.PolynomialExp
  - Mathlib.Analysis.SpecialFunctions.Bernstein
  - Mathlib.Analysis.SpecialFunctions.Choose
  - Mathlib.Analysis.SpecialFunctions.Pochhammer
  - Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean
explains:
  E2: [Real.sigmoid_neg, Real.hasDerivAt_sigmoid, expNegInvGlue.zero_of_nonpos, Real.smoothTransition.one_of_one_le, Real.abs_mulExpNegMulSq_le, bernstein.probability, NNReal.dist_agmSequences_fst_snd, NNReal.agm_mul_distrib]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C02, V15.C03, V15.C05, V15.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Auxiliary functions, Bernstein polynomials and the arithmetic-geometric mean

### Overview

The elementary functions of Chapters 5 and 6 build many special functions with a single purpose. Other parts of Mathlib use these functions as tools. The sigmoid $\sigma(x) = 1/(1 + e^{-x})$ is a smooth order isomorphism from $\mathbb{R}$ onto $(0, 1)$. The function $e^{-1/x}$ glues smoothly to $0$ at the origin, and it gives a smooth step from $0$ to $1$. The function $x e^{-\varepsilon x^2}$ cuts a real function down to a bounded function. The Japanese bracket $(1 + \|x\|^2)^{1/2}$ is a smooth substitute for $1 + \|x\|$ in the estimates of Fourier analysis.

This section also treats three results of a more classical kind. The Bernstein polynomials prove the Weierstrass approximation theorem. The binomial coefficient $\binom{n}{k}$ is asymptotic to $n^k/k!$, and the descending Pochhammer polynomial is convex, which gives a Jensen inequality for $\binom{n}{k}$. The arithmetic-geometric mean is the common limit of two sequences of means. Each module is short, and each module uses only the derivatives, the limits and the exponential of the earlier chapters, with the notation $\sim$ and $\Theta$ of Chapter 7.

### The library around it

#### The sigmoid function

The module `Mathlib.Analysis.SpecialFunctions.Sigmoid` defines `Real.sigmoid` with `Real.sigmoid_def`: $\sigma(x) = (1 + e^{-x})^{-1}$. The basic facts are `Real.sigmoid_pos`, `Real.sigmoid_lt_one`, `Real.sigmoid_zero` ($\sigma(0) = 1/2$), the limits `Real.tendsto_sigmoid_atTop` and `Real.tendsto_sigmoid_atBot`, and `Real.range_sigmoid`: the range is the open interval $(0, 1)$.

**Theorem.** $\sigma(-x) = 1 - \sigma(x)$, and $\sigma'(x) = \sigma(x)\,(1 - \sigma(x))$.

*Proof.* Put $u = e^{-x}$. Then $\sigma(-x) = 1/(1 + 1/u) = u/(1 + u) = 1 - 1/(1 + u) = 1 - \sigma(x)$. For the derivative, the chain rule gives $\sigma'(x) = e^{-x}/(1 + e^{-x})^2 = \sigma(x) \cdot u/(1 + u) = \sigma(x)\,\sigma(-x)$, and the first identity finishes the proof. $\square$

These are `Real.sigmoid_neg` and `Real.hasDerivAt_sigmoid`, with `Real.deriv_sigmoid` for the function `deriv`. The order lemmas follow the usual pattern: `Real.sigmoid_strictMono`, `Real.sigmoid_le_iff`, `Real.sigmoid_lt_iff` and `Real.sigmoid_inj`. The regularity lemmas come in two forms. The lemmas with a lower-case name, such as `contDiff_sigmoid`, `differentiable_sigmoid` and `analyticOnNhd_sigmoid`, are about $\sigma$ itself. The lemmas in the namespace of a property, such as `ContDiff.sigmoid`, `Differentiable.sigmoid` and `AnalyticAt.sigmoid`, are about a composition $\sigma \circ f$, so that `fun_prop` and dot notation can use them.

The module also views $\sigma$ as a map into the unit interval `unitInterval` of Volume 13. The function `unitInterval.sigmoid` has the same values, `OrderEmbedding.sigmoid` packs it as an order embedding, and `Topology.isEmbedding_sigmoid` and `measurableEmbedding_sigmoid` state that it is a topological and a measurable embedding. With the embedding of a standard Borel space into $\mathbb{R}$, `measurableEmbedding_sigmoid_comp_embeddingReal` embeds every standard Borel space into $[0, 1]$. Probability theory uses this fact.

#### Smooth gluing and the smooth step

The module `Mathlib.Analysis.SpecialFunctions.SmoothTransition` defines `expNegInvGlue`: the function equal to $e^{-1/x}$ for $x > 0$ and to $0$ for $x \le 0$. The lemmas `expNegInvGlue.zero_of_nonpos`, `expNegInvGlue.pos_of_pos` and `expNegInvGlue.zero_iff_nonpos` state its sign. The key result is `expNegInvGlue.contDiff`: the function is $C^n$ for each $n$. The proof is an induction with the family `expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul`. For a polynomial $p$, the derivative of $p(1/x)\,e^{-1/x}$ is $q(1/x)\,e^{-1/x}$ with $q = X^2(p - p')$. Each such function tends to $0$ at $0$ (`expNegInvGlue.tendsto_polynomial_inv_mul_zero`), because $e^{-1/x}$ is smaller than every power of $x$. All the derivatives at $0$ are then $0$, and `expNegInvGlue.not_analyticAt_zero` states that the function is not analytic at $0$. It is the standard example of a smooth function that is not analytic.

The smooth step `Real.smoothTransition` is
$$s(x) = \frac{g(x)}{g(x) + g(1 - x)}, \qquad g = \texttt{expNegInvGlue}.$$
The denominator is positive (`Real.smoothTransition.pos_denom`), because $x > 0$ or $1 - x > 0$.

**Theorem.** $s(x) = 0$ for $x \le 0$ and $s(x) = 1$ for $x \ge 1$.

*Proof.* For $x \le 0$ the numerator $g(x)$ is $0$. For $x \ge 1$, $1 - x \le 0$, so $g(1 - x) = 0$ and $s(x) = g(x)/g(x) = 1$, with $g(x) > 0$. $\square$

These are `Real.smoothTransition.zero_of_nonpos` and `Real.smoothTransition.one_of_one_le`. The module also has `Real.smoothTransition.nonneg`, `Real.smoothTransition.le_one`, `Real.smoothTransition.monotone` and `Real.smoothTransition.contDiff`. The smooth bump functions of Volume 17 and the partitions of unity of Volume 23 are built from this step.

#### The cut-off $x e^{-\varepsilon x^2}$

The module `Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq` defines `Real.mulExpNegMulSq`, with `Real.mulExpNegSq_apply`: `Real.mulExpNegMulSq ε x` is $x\,e^{-\varepsilon x^2}$. For fixed $\varepsilon > 0$ the function is bounded and $1$-Lipschitz, and as $\varepsilon \to 0$ it tends to the identity.

**Theorem.** For $\varepsilon > 0$ and all $x$, $|x e^{-\varepsilon x^2}| \le 1/\sqrt{\varepsilon}$.

*Proof.* Put $y = \sqrt{\varepsilon}\,x$. Then $x e^{-\varepsilon x^2} = \varepsilon^{-1/2}\, y e^{-y^2}$, and it is enough to show $|y| e^{-y^2} \le 1$. This follows from $e^{y^2} \ge 1 + y^2 \ge |y|$, where the last step is $|y| \le 1 + y^2$. $\square$

The scaling step is `Real.mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one`, the case $\varepsilon = 1$ is `Real.abs_mulExpNegMulSq_one_le_one`, and the result is `Real.abs_mulExpNegMulSq_le`. The other lemmas are `Real.lipschitzWith_one_mulExpNegMulSq`, `Real.norm_deriv_mulExpNegMulSq_le_one`, `Real.tendsto_mulExpNegMulSq` and `Real.abs_mulExpNegMulSq_comp_le_norm`. The last one bounds `Real.mulExpNegMulSq ε ∘ g` by the sup norm of a bounded continuous function $g$. A proof that two finite measures are equal when they integrate the same bounded functions uses this cut-off, and the integral facts are in `Mathlib.Analysis.SpecialFunctions.MulExpNegMulSqIntegral`, in the section on integrals of this chapter.

#### The Japanese bracket

The module `Mathlib.Analysis.SpecialFunctions.JapaneseBracket` compares $\langle x \rangle = (1 + \|x\|^2)^{1/2}$ with $1 + \|x\|$ in a normed space $E$. The two inequalities are `sqrt_one_add_norm_sq_le`, $\langle x \rangle \le 1 + \|x\|$, and `one_add_norm_le_sqrt_two_mul_sqrt`, $1 + \|x\| \le \sqrt{2}\,\langle x \rangle$. For $E$ of finite dimension $d$ with a Haar measure, `integrable_one_add_norm` states that $(1 + \|x\|)^{-r}$ is integrable for $r > d$, and `integrable_rpow_neg_one_add_norm_sq` states the same for $\langle x \rangle^{-r}$. The integrals need the measure theory of Volume 18. The proof computes the measure of the sets where $(1 + \|x\|)^{-r} \ge t$, with `le_rpow_one_add_norm_iff_norm_le`.

#### Polynomials against the exponential

The module `Mathlib.Analysis.SpecialFunctions.PolynomialExp` has one theorem, `Polynomial.tendsto_div_exp_atTop`: for each real polynomial $P$, $P(x)/e^x \to 0$ as $x \to \infty$. It follows from the limits $x^n e^{-x} \to 0$ of Chapter 7 by linearity.

#### Bernstein polynomials and the Weierstrass theorem

The module `Mathlib.Analysis.SpecialFunctions.Bernstein` defines `bernstein n ν` as a continuous function on $[0, 1]$, with `bernstein_apply`:
$$b_{n,\nu}(x) = \binom{n}{\nu} x^\nu (1 - x)^{n - \nu}.$$
The points $k/n$ for $k = 0, \dots, n$ are `bernstein.z k`. For a continuous function $f : [0, 1] \to E$, the Bernstein approximation `bernsteinApproximation n f` is $\sum_k b_{n,k}(x)\, f(k/n)$ (`bernsteinApproximation.apply`). Two identities do the work. The first is `bernstein.probability`: $\sum_{k=0}^{n} b_{n,k}(x) = 1$. It is the binomial theorem for $(x + (1 - x))^n$. The second is `bernstein.variance`: $\sum_k (x - k/n)^2\, b_{n,k}(x) = x(1 - x)/n$. In the language of probability, $b_{n,k}(x)$ is the law of a binomial variable, and the identities give its mean and its variance.

The main theorem is `bernsteinApproximation_uniform`: the approximations converge to $f$ in the topology of uniform convergence on $C([0, 1], E)$, for every locally convex space $E$. The proof splits the sum into the terms with $|x - k/n| < \delta$ and the other terms. The first part is small by uniform continuity of $f$, from Chapter 2. The second part is small by the variance identity, as in Chebyshev's inequality. The Weierstrass theorem follows: the polynomials are dense in $C([0, 1], \mathbb{R})$.

#### Binomial coefficients and Pochhammer polynomials

The module `Mathlib.Analysis.SpecialFunctions.Choose` has three asymptotic results for fixed $k$ as $n \to \infty$. `isEquivalent_descFactorial` states $n(n-1)\cdots(n-k+1) \sim n^k$, `isEquivalent_choose` states $\binom{n}{k} \sim n^k/k!$, and `isTheta_choose` states $\binom{n}{k} = \Theta(n^k)$.

The module `Mathlib.Analysis.SpecialFunctions.Pochhammer` studies the evaluation of the descending Pochhammer polynomial `descPochhammer ℝ n`, the polynomial $x(x-1)\cdots(x-n+1)$. It is continuous and differentiable (`continuous_descPochhammer_eval`, `differentiable_descPochhammer_eval`), and `deriv_descPochhammer_eval_eq_sum_prod_range_erase` writes its derivative with the product rule. The derivative is monotone on $(n - 1, \infty)$ (`monotoneOn_deriv_descPochhammer_eval`), so the polynomial is convex on $[n - 1, \infty)$ (`convexOn_descPochhammer_eval`). Jensen's inequality then gives `descPochhammer_eval_le_sum_descFactorial` and `descPochhammer_eval_div_factorial_le_sum_choose`: for weights $w_i \ge 0$ with $\sum w_i = 1$ and natural numbers $p_i$ with $\sum w_i p_i \ge n - 1$,
$$\binom{\sum_i w_i p_i}{n} \le \sum_i w_i \binom{p_i}{n},$$
where the left side is the value of the polynomial divided by $n!$. Extremal combinatorics uses this inequality.

#### The arithmetic-geometric mean

The module `Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean` works in `NNReal`. For $x, y \ge 0$, `NNReal.agmSequences x y n` is the pair $(g_n, a_n)$, where $(g_0, a_0) = (\sqrt{xy}, (x + y)/2)$ and each step replaces the pair by its geometric and its arithmetic mean (`NNReal.agmSequences_zero`, `NNReal.agmSequences_succ'`). Note that the index $0$ is already one step of the iteration. The inequality of the means, `NNReal.sqrt_mul_le_half_add`, gives $g_n \le a_m$ for all $n, m$ (`NNReal.agmSequences_fst_le_snd`). The sequence $(g_n)$ increases and $(a_n)$ decreases (`NNReal.agmSequences_monotone_and_antitone`).

**Theorem.** $|g_n - a_n| \le |x - y|/2^{n+1}$.

*Proof.* For $u \le v$, $u \le \sqrt{uv} \le (u + v)/2 \le v$, and $(u + v)/2 - \sqrt{uv} \le (u + v)/2 - u = (v - u)/2$. So each step at least halves the distance (`NNReal.dist_gm_am_le`). The first step gives the factor $1/2$, and induction gives the factor $1/2^{n+1}$. $\square$

This is `NNReal.dist_agmSequences_fst_snd`. So both sequences converge to the same limit, `NNReal.agm x y` (`NNReal.tendsto_agmSequences_fst_agm`, `NNReal.tendsto_agmSequences_snd_agm`). The definition is the supremum of the $g_n$, and `NNReal.agm_eq_ciSup` and `NNReal.agm_eq_ciInf` give the two descriptions. The algebraic rules are `NNReal.agm_comm`, `NNReal.agm_self`, `NNReal.agm_zero_left`, `NNReal.agm_eq_agm_gm_am` and `NNReal.agm_mul_distrib`: $\operatorname{agm}(kx, ky) = k \operatorname{agm}(x, y)$, because $\sqrt{kx \cdot ky} = k\sqrt{xy}$ and $(kx + ky)/2 = k(x + y)/2$, so the two sequences scale by $k$. The bounds are `NNReal.min_le_agm` and `NNReal.agm_le_max`, with strict forms for $x \ne y$.

#### Common errors

1. Two sigmoid functions exist. `Real.sigmoid` has values in `ℝ`, and `unitInterval.sigmoid` has values in the subtype $[0, 1]$. A lemma about one does not rewrite the other, and the coercion links them.
2. `Real.smoothTransition` is a step from $0$ at $x \le 0$ to $1$ at $x \ge 1$. It is not a bump function. A bump with compact support needs a product of two steps, or the structure `ContDiffBump` of Volume 17.
3. In `NNReal.agmSequences x y n` the index $0$ is the pair $(\sqrt{xy}, (x + y)/2)$, not the pair $(x, y)$. A computation by hand must shift the index by one.

### Exercises

1. (A) Show that $\sigma(x) + \sigma(-x) = 1$ and that $\sigma$ satisfies $\sigma' = \sigma(1 - \sigma)$. Deduce that $\sigma'$ has its maximum $1/4$ at $0$.
2. (A) Compute $b_{2,0}, b_{2,1}, b_{2,2}$ and the Bernstein approximation of $f(x) = x^2$ of order $n$. Show that it is $x^2 + x(1-x)/n$.
3. (B) Show that every derivative of $e^{-1/x}$ at $x \to 0^+$ tends to $0$, with the polynomial form $p(1/x)\,e^{-1/x}$ of the derivatives. Deduce that `expNegInvGlue` has a zero Taylor series at $0$.
4. (B) Show that $\operatorname{agm}(1, 2)$ lies strictly between $\sqrt{2}$ and $3/2$, and compute it to three decimal places with two steps of the iteration.
5. (B) Prove $\binom{n}{2} \sim n^2/2$ directly, and state the result of `isEquivalent_choose` for $k = 3$.
6. (C) Prove the Weierstrass theorem on $[0, 1]$ from `bernstein.probability` and `bernstein.variance`: for a continuous $f$ and $\varepsilon > 0$, find $n$ with $|B_n f(x) - f(x)| < \varepsilon$ for all $x$. Hint: split the sum at $|x - k/n| < \delta$ and bound the second part by $\frac{2\|f\|}{\delta^2} \sum_k (x - k/n)^2 b_{n,k}(x)$.

### Reference

<?reference?>
