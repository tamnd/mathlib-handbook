---
title: Characteristic functions and the convergence theorem of Lévy
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
  - Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
  - Mathlib.MeasureTheory.Measure.IntegralCharFun
  - Mathlib.MeasureTheory.Measure.LevyConvergence
  - Mathlib.MeasureTheory.Measure.ResolventTransform
explains:
  E2: [MeasureTheory.charFun, MeasureTheory.charFunDual, MeasureTheory.Measure.ext_of_charFun, MeasureTheory.charFun_conv, MeasureTheory.charFun_eq_prod_iff, MeasureTheory.iteratedDeriv_charFun_zero, MeasureTheory.measureReal_abs_gt_le_integral_charFun, MeasureTheory.isTightMeasureSet_of_tendsto_charFun, MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun, MeasureTheory.resolventTransform]
  E1: auto
families: []
requires: [V13, V15, V16, V18.C04, V18.C05, V18.C06, V18.C08, V18.C09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Characteristic functions and the convergence theorem of Lévy

### Overview

The characteristic function of a finite measure $\mu$ on an inner product space $E$ is

$$\varphi_\mu(t) = \int e^{i \langle x, t \rangle} \, d\mu(x), \qquad t \in E.$$

It is the Fourier transform of $\mu$, up to the sign and the factor $2\pi$ in the exponent. Three properties make it the main tool for limit theorems. It determines the measure. It turns convolution into multiplication: the characteristic function of the law of a sum of independent random variables is the product of the characteristic functions. And the convergence theorem of Lévy says that, in finite dimension, $\mu_n \to \mu$ weakly if and only if $\varphi_{\mu_n}(t) \to \varphi_\mu(t)$ for every $t$.

This section describes the definition and the computation rules, the uniqueness theorem, the derivatives at $0$ and the moments, the bound of the tails by an integral of $\varphi_\mu$ near $0$, the theorem of Lévy, and the resolvent transform, a related transform for measures on $\mathbb{R}$ or $\mathbb{C}$.

### The library around it

#### The definition

The characteristic function `MeasureTheory.charFun μ` is defined on a real inner product space, and `MeasureTheory.charFun_apply` gives its value as the integral of `Complex.exp (⟪x, t⟫ * I)`. On $\mathbb{R}$ the inner product is the product, `MeasureTheory.charFun_apply_real`. For a normed space without an inner product, the variable is a continuous linear form: `MeasureTheory.charFunDual μ L` is $\int e^{i L(x)} \, d\mu(x)$ for $L$ in the dual space. On an inner product space the two agree through the Riesz map, `MeasureTheory.charFun_eq_charFunDual_toDualMap`. The connection with the Fourier transform of Mathlib is `MeasureTheory.charFun_eq_fourierIntegral`.

The basic values: $\varphi_\mu(0) = \mu(E)$, `MeasureTheory.charFun_zero`, and $|\varphi_\mu(t)| \le 1$ for a probability measure, `MeasureTheory.norm_charFun_le_one`. For a point mass, $\varphi_{\delta_x}(t) = e^{i \langle x, t \rangle}$, `MeasureTheory.charFun_dirac`. The value at $-t$ is the complex conjugate of the value at $t$, `MeasureTheory.charFun_neg`, since $e^{-i\theta}$ is the conjugate of $e^{i\theta}$. Under a translation by $a$, the image measure has the characteristic function $\varphi_\mu(t) e^{i \langle a, t \rangle}$, `MeasureTheory.charFun_map_const_add`. On $\mathbb{R}$, the image under $x \mapsto c x$ has the characteristic function $\varphi_\mu(c t)$, `MeasureTheory.charFun_map_mul`. The function is continuous for a finite $\mu$, `MeasureTheory.continuous_charFun`, by dominated convergence with the bound $1$.

#### Products, convolutions and uniqueness

For the convolution of two finite measures, `MeasureTheory.charFun_conv` gives $\varphi_{\mu * \nu} = \varphi_\mu \varphi_\nu$. The proof is Fubini: $e^{i \langle x + y, t \rangle} = e^{i \langle x, t \rangle} e^{i \langle y, t \rangle}$. For a product measure on $E \times F$, with the inner product of `WithLp 2 (E × F)`, the characteristic function is the product of the two, `MeasureTheory.charFun_prod`. The variants for finite products are `MeasureTheory.charFun_pi` and `MeasureTheory.charFunDual_pi`.

The uniqueness theorem is `MeasureTheory.Measure.ext_of_charFun`: on a complete separable inner product space, two finite measures with the same characteristic function are equal. The proof is `MeasureTheory.ext_of_integral_char_eq`, an application of the result of Section 1 on separating algebras. The functions $x \mapsto e^{i \langle x, t \rangle}$, the bounded continuous functions `BoundedContinuousFunction.innerProbChar`, span a star subalgebra that separates points, and two measures that agree on its elements are equal. The dual form is `MeasureTheory.Measure.ext_of_charFunDual`. With uniqueness, the product formula becomes a criterion of independence, `MeasureTheory.charFun_eq_prod_iff`: a finite measure $\xi$ on $E \times F$ is the product $\mu \otimes \nu$ if and only if its characteristic function is $\varphi_\mu(t_1) \varphi_\nu(t_2)$.

#### Moments and the Taylor expansion

If $\mu$ has a finite moment of order $n$, then $\varphi_\mu$ is $n$ times continuously differentiable, `MeasureTheory.contDiff_charFun`. The derivatives are integrals with powers of $\langle x, \cdot \rangle$, `MeasureTheory.iteratedFDeriv_charFun`. On $\mathbb{R}$, `MeasureTheory.iteratedDeriv_charFun_zero` gives the moments:

$$\varphi_\mu^{(n)}(0) = i^n \int x^n \, d\mu(x).$$

For a random variable $X$ with mean $0$ and variance $1$, the expansion of order $2$ is `MeasureTheory.taylor_charFun_two`:

$$\varphi_X(t) = 1 - \frac{t^2}{2} + o(t^2) \quad (t \to 0).$$

This is the step of the central limit theorem: for a sum of $n$ independent copies divided by $\sqrt{n}$, the characteristic function is $(1 - t^2/(2n) + o(1/n))^n \to e^{-t^2/2}$.

#### The tails and the integral of the characteristic function

The file `Mathlib.MeasureTheory.Measure.IntegralCharFun` bounds the mass far from $0$ by the behavior of $\varphi_\mu$ near $0$. The integral of $\varphi_\mu$ over $[-r, r]$ is an integral of the function $\operatorname{sinc}$, `MeasureTheory.integral_charFun_Icc`:

$$\int_{-r}^{r} \varphi_\mu(t) \, dt = 2r \int \operatorname{sinc}(r x) \, d\mu(x).$$

From it, `MeasureTheory.measureReal_abs_gt_le_integral_charFun` gives, for a probability measure on $\mathbb{R}$ and $r > 0$,

$$\mu(\{x : |x| > r\}) \le \frac{r}{2} \Big| \int_{-2/r}^{2/r} (1 - \varphi_\mu(t)) \, dt \Big|.$$

The right side is small when $\varphi_\mu$ is close to $1$ near $0$. The forms for the projections $\langle y, x \rangle$ in an inner product space and for linear forms are `MeasureTheory.measureReal_abs_inner_gt_le_integral_charFun` and `MeasureTheory.measureReal_abs_dual_gt_le_integral_charFunDual`.

#### The convergence theorem of Lévy

The file `Mathlib.MeasureTheory.Measure.LevyConvergence` proves the theorem in a finite dimensional inner product space. The first step is tightness. If $\varphi_{\mu_n}(t) \to f(t)$ for every $t$, with $f$ continuous at $0$, then the sequence $(\mu_n)$ is tight, `MeasureTheory.isTightMeasureSet_of_tendsto_charFun`. The proof uses the bound of the tails above for each projection, dominated convergence on $[-2/r, 2/r]$, and the criterion of Section 3 with inner products.

The second step uses the separating algebra again. A tight sequence whose integrals converge for every element of a separating star subalgebra converges weakly, `MeasureTheory.ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`. The proof applies the theorem of Prokhorov of Section 3: every subsequence has a further subsequence with a weak limit, and the limit is $\mu$ by the uniqueness from the algebra. The integrals of the trigonometric polynomials converge when the characteristic functions converge, `MeasureTheory.ProbabilityMeasure.tendsto_charPoly_of_tendsto_charFun`.

The result is `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`: in a finite dimensional inner product space, a sequence of probability measures converges weakly to $\mu$ if and only if the characteristic functions converge pointwise to $\varphi_\mu$. The direction from characteristic functions to weak convergence alone is `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`. For random variables, the form with convergence in distribution is `MeasureTheory.tendstoInDistribution_iff_tendsto_charFun`.

#### The resolvent transform

The file `Mathlib.MeasureTheory.Measure.ResolventTransform` defines, for a finite measure $\mu$ on $\mathbb{R}$ or $\mathbb{C}$ and $a$ in a normed algebra $A$, the transform `MeasureTheory.resolventTransform μ a`, the integral of the resolvent $(x - a)^{-1}$:

$$s_\mu(a) = \int \frac{d\mu(x)}{x - a}.$$

For $A = \mathbb{C}$ and $\mu$ on $\mathbb{R}$, this is the Stieltjes transform of $\mu$. The value is `MeasureTheory.resolventTransform_apply`, and for a point mass it is the resolvent at that point, `MeasureTheory.resolventTransform_dirac`. Off the support of $\mu$, the resolvent is bounded by the inverse of the distance to the support, `MeasureTheory.norm_resolvent_le_inv_infDist_support`. So the transform is analytic on the complement of the support, `MeasureTheory.analyticOn_resolventTransform`, with the derivative $\int (x - a)^{-2} \, d\mu(x)$, `MeasureTheory.hasDerivAt_resolventTransform`.

#### Common errors

1. Using the convention of the Fourier transform. `MeasureTheory.charFun` has the exponent $i \langle x, t \rangle$ with no factor $2\pi$ and a plus sign; the Fourier transform of Mathlib has $-2\pi i \langle x, t \rangle$. Convert with `MeasureTheory.charFun_eq_fourierIntegral`.
2. Applying the theorem of Lévy in infinite dimension. `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun` needs a finite dimensional space; in a Hilbert space of infinite dimension the pointwise convergence of characteristic functions does not imply tightness.
3. Forgetting the continuity at $0$ of the limit. A pointwise limit of characteristic functions that is not continuous at $0$ comes from a sequence that loses mass: the Gaussian laws with variance $n$ have the characteristic functions $e^{-n t^2/2}$, which tend to the indicator of $\{0\}$.

### Exercises

1. (A) Compute `MeasureTheory.charFun` of the measure $\frac{1}{2}(\delta_{-1} + \delta_1)$ on $\mathbb{R}$ with `MeasureTheory.charFun_dirac`.
2. (A) Use `MeasureTheory.iteratedDeriv_charFun_zero` to compute the mean and the second moment of a probability measure with the characteristic function $\cos t$.
3. (B) Prove `MeasureTheory.charFun_conv` from the theorem of Fubini and the identity $e^{i(a + b)} = e^{ia} e^{ib}$.
4. (B) Let $\mu_n$ be the uniform probability measure on $[-n, n]$. Compute $\varphi_{\mu_n}$, find its pointwise limit, and explain why the sequence is not tight.
5. (B) Show that $\varphi_\mu$ is real for every $t$ when $\mu$ is symmetric, $\mu(-A) = \mu(A)$, with `MeasureTheory.charFun_neg` and `MeasureTheory.Measure.ext_of_charFun`, and prove the converse.
6. (C) Use `MeasureTheory.taylor_charFun_two` and `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun` to prove the central limit theorem for a sequence of independent random variables with the same law, mean $0$ and variance $1$.

### Reference

<?reference?>
