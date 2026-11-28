---
title: Convolution of functions and measures
kind: api
modules:
  - Mathlib.Analysis.Convolution
  - Mathlib.Analysis.LConvolution
  - Mathlib.MeasureTheory.Group.Convolution
  - Mathlib.MeasureTheory.Group.IntegralConvolution
explains:
  E2: [MeasureTheory.convolution, MeasureTheory.ConvolutionExistsAt, MeasureTheory.ConvolutionExists, MeasureTheory.convolution_def, HasCompactSupport.continuous_convolution_right, MeasureTheory.integral_convolution, MeasureTheory.convolution_tendsto_right, MeasureTheory.lconvolution, MeasureTheory.Measure.conv, MeasureTheory.integral_conv]
  E1: auto
families: []
requires: [V13, V18.C04, V18.C05, V18.C06, V18.C07, V18.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Convolution of functions and measures

### Overview

The convolution of two functions on $\mathbb{R}^n$ is
$$(f * g)(x) = \int f(t) \, g(x - t) \, dt.$$
It averages $g$ with the weights of $f$. Convolution with a smooth bump of small support gives smooth functions close to $g$. The Fourier transform turns convolution into a product. The sum of two independent random variables has as its law the convolution of the two laws.

Mathlib has three forms of convolution. The convolution `MeasureTheory.convolution` of functions with values in normed spaces is a Bochner integral, and it takes a continuous bilinear map to multiply the values. The convolution `MeasureTheory.lconvolution` of functions with values in $[0, \infty]$ is a lower integral. The convolution `MeasureTheory.Measure.conv` of two measures is the image of the product measure under addition. This section explains the three forms and the main theorems about them.

The section needs the integrals of Chapters 4 and 5, the theorem of Fubini of Chapter 6, the spaces $L^p$ of Chapter 7, the interval integral of Chapter 8 and the invariant measures of Section 1 of this chapter.

### The library around it

#### The convolution of functions

The function `MeasureTheory.convolution f g L μ` takes $f : G \to E$, $g : G \to E'$, a continuous bilinear map `L : E →L[𝕜] E' →L[𝕜] F` and a measure on an additive group `G`. The lemma `MeasureTheory.convolution_def` gives its value:
$$(f * g)(x) = \int L(f(t), g(x - t)) \, d\mu(t).$$
The bilinear map makes one definition cover many cases. For scalar functions, `L` is the multiplication `ContinuousLinearMap.mul 𝕜 𝕜`, and `MeasureTheory.convolution_mul` gives the usual formula. For a scalar function and a vector function, `L` is `ContinuousLinearMap.lsmul ℝ ℝ`, and `MeasureTheory.convolution_lsmul` gives $\int f(t) \, g(x - t) \, d\mu(t)$ with scalar multiplication. The notation `f ⋆[L, μ] g` for this function is available after `open Convolution`.

The integral has the junk value $0$ when the integrand is not integrable. The predicate `MeasureTheory.ConvolutionExistsAt f g x L μ` says that the integrand at $x$ is integrable, and `MeasureTheory.ConvolutionExists f g L μ` says that this holds at every $x$. Most theorems about the value need one of these predicates.

#### When the convolution exists

The library has several sufficient conditions:

| Lean name | Hypotheses |
|---|---|
| `HasCompactSupport.convolutionExists_right` | $g$ continuous with compact support, $f$ locally integrable |
| `HasCompactSupport.convolutionExists_left` | the same with the roles of $f$ and $g$ exchanged |
| `MeasureTheory.ConvolutionExists.of_memLp_memLp` | $f \in L^p$, $g \in L^q$ with conjugate exponents |
| `MeasureTheory.Integrable.ae_convolution_exists` | $f$ and $g$ integrable: the convolution exists almost everywhere |
| `BddAbove.convolutionExistsAt` | $g$ bounded and $f$ integrable on a suitable translate of the support |

The case of compact support is the one for mollifiers. The case of $L^p$ and $L^q$ rests on the inequality of Hölder: `MeasureTheory.eLpNorm_convolution_integrand_le` bounds the seminorm of the integrand by $\|L\| \, \|f\|_p \, \|g\|_q$. The case of two integrable functions rests on the theorem of Fubini, and the convolution is integrable again, by `MeasureTheory.Integrable.integrable_convolution`. Most of these results need the measure to be invariant under addition and under negation, and σ-finite.

#### Algebraic rules

The convolution is bilinear: `MeasureTheory.ConvolutionExistsAt.distrib_add`, `MeasureTheory.ConvolutionExistsAt.add_distrib`, `MeasureTheory.smul_convolution` and `MeasureTheory.convolution_smul`. The lemmas `MeasureTheory.zero_convolution` and `MeasureTheory.convolution_zero` treat the zero function. Exchanging the two functions exchanges the arguments of `L`: `MeasureTheory.convolution_flip` states `convolution g f L.flip μ = convolution f g L μ`. The form with the translation on the other factor is `MeasureTheory.convolution_eq_swap`. For scalar functions on a commutative ring, `MeasureTheory.convolution_mul_swap` gives commutativity in the usual form.

Associativity needs a compatibility of four bilinear maps, which says that $L_2(L(x, y), z) = L_3(x, L_4(y, z))$. Under this condition and integrability hypotheses, `MeasureTheory.convolution_assoc` gives $(f * g) * k = f * (g * k)$. The support of a convolution lies in the sum of the supports, by `MeasureTheory.support_convolution_subset`, and a convolution of functions with compact support has compact support, by `HasCompactSupport.convolution`.

The integral of a convolution is the product of the integrals, by `MeasureTheory.integral_convolution`:
$$\int (f * g) \, d\mu = L\Big(\int f \, d\nu, \int g \, d\mu\Big).$$

#### Regularity

Convolution with a continuous function of compact support gives a continuous function. The lemma `HasCompactSupport.continuous_convolution_right` says that $f * g$ is continuous when $f$ is locally integrable and $g$ is continuous with compact support. The lemma `HasCompactSupport.continuous_convolution_left` exchanges the roles. The lemma `BddAbove.continuous_convolution_right_of_integrable` replaces compact support by boundedness and integrability. For convolutions that depend on a parameter, `MeasureTheory.continuousOn_convolution_right_with_param` gives continuity in both variables. The smoothness of convolutions, which uses derivatives, is in Volume 17.

#### Approximate identities

A family $\varphi_i$ of nonnegative functions with integral $1$ whose supports shrink to $0$ is an approximate identity. The lemma `MeasureTheory.dist_convolution_le` is the basic estimate. If the support of $\varphi$ lies in the ball of radius $R$ and $g$ stays within $\varepsilon$ of $z_0$ on the ball of radius $R$ about $x_0$, then $(\varphi * g)(x_0)$ is within $\varepsilon$ of $z_0$. The lemma `MeasureTheory.convolution_tendsto_right` turns this into a limit: if $g$ is continuous at $x_0$, then $(\varphi_i * g)(k_i) \to g(x_0)$ for every family of points $k_i \to x_0$. This is the base of approximation by smooth functions.

#### Convolution on the positive half line

The function `MeasureTheory.posConvolution f g L ν` is the convolution of functions on the positive half line:
$$x \mapsto \int_0^x L(f(t), g(x - t)) \, dt \quad \text{for } x > 0,$$
and $0$ for $x \le 0$. The lemma `MeasureTheory.posConvolution_eq_convolution_indicator` identifies it with the convolution of the indicators of $(0, \infty)$ times $f$ and $g$. The lemmas `MeasureTheory.integrable_posConvolution` and `MeasureTheory.integral_posConvolution` give its integrability and integral. The Beta function of Volume 19 is a convolution of this kind.

#### Convolution with values in $[0, \infty]$

The file `Mathlib.Analysis.LConvolution` defines `MeasureTheory.lconvolution f g μ`, the function $x \mapsto \int^{-} f(y) \, g(x - y) \, d\mu(y)$ for $f, g : G \to [0, \infty]$. The multiplicative version is `MeasureTheory.mlconvolution`, with $g(y^{-1} x)$, and `MeasureTheory.mlconvolution_def` states its definition. It needs no existence predicate, since every lower integral exists. The lemmas `MeasureTheory.lconvolution_comm` and `MeasureTheory.lconvolution_assoc` give commutativity and associativity for an invariant measure, and `MeasureTheory.measurable_lconvolution` gives measurability.

#### Convolution of measures

The file `Mathlib.MeasureTheory.Group.Convolution` defines `MeasureTheory.Measure.mconv μ ν` as the image of `μ.prod ν` under multiplication. The additive version `MeasureTheory.Measure.conv μ ν` uses addition. In probability, the law of $X + Y$ for independent $X$ and $Y$ is the convolution of their laws.

| Lean name | Statement |
|---|---|
| `MeasureTheory.Measure.lintegral_conv` | $\int^{-} f \, d(\mu * \nu) = \int^{-} \int^{-} f(x + y) \, d\nu(y) \, d\mu(x)$ |
| `MeasureTheory.Measure.dirac_conv_dirac` | $\delta_x * \delta_y = \delta_{x + y}$ |
| `MeasureTheory.Measure.dirac_conv` | $\delta_x * \mu$ is the translate of $\mu$ by $x$ |
| `MeasureTheory.Measure.conv_comm` | $\mu * \nu = \nu * \mu$ for s-finite measures on a commutative group |
| `MeasureTheory.Measure.conv_assoc` | $(\mu * \nu) * \rho = \mu * (\nu * \rho)$ |
| `MeasureTheory.Measure.map_conv_addMonoidHom` | an additive homomorphism maps a convolution to the convolution of the images |
| `MeasureTheory.Measure.conv_absolutelyContinuous` | if $\nu \ll \rho$ for an invariant $\rho$, then $\mu * \nu \ll \rho$ |

The convolution of two probability measures is a probability measure, by `MeasureTheory.Measure.probabilitymeasure_of_probabilitymeasures_conv`. The file `Mathlib.MeasureTheory.Group.IntegralConvolution` gives the Bochner form: `MeasureTheory.integral_conv` states
$$\int f \, d(\mu * \nu) = \int \int f(x + y) \, d\nu(y) \, d\mu(x)$$
for an integrable $f$, and `MeasureTheory.integrable_conv_iff` characterizes integrability against $\mu * \nu$.

#### Common errors

1. Forgetting the bilinear map. The convolution of two real functions is `convolution f g (ContinuousLinearMap.mul ℝ ℝ) μ`, or `ContinuousLinearMap.lsmul ℝ ℝ` for the form that most lemmas about approximate identities use.
2. Using the value of `MeasureTheory.convolution` at a point where the integrand is not integrable. The value is then $0$. Prove `MeasureTheory.ConvolutionExistsAt` first.
3. Confusing the convolution of measures with the convolution of densities. They agree only through the density: the convolution of $f \mu$ and $g \mu$ is $(f * g) \mu$ for a Haar measure $\mu$.

### Exercises

1. (A) Compute the convolution $\mathbf{1}_{[0,1]} * \mathbf{1}_{[0,1]}$ on $\mathbb{R}$.
2. (A) Show that $\delta_x * \delta_y = \delta_{x + y}$ from the definition of the convolution of measures.
3. (B) Show that the convolution of a locally integrable function with a continuous function with compact support is continuous.
4. (B) Show that $\int (f * g) = (\int f)(\int g)$ for integrable real functions on $\mathbb{R}$.
5. (B) Show that the convolution of two Gaussian probability measures on $\mathbb{R}$ with means $0$ and variances $s$ and $t$ is the Gaussian with variance $s + t$.
6. (C) Prove that $\varphi_n * g \to g$ uniformly on compact sets for a continuous $g$ and an approximate identity $\varphi_n$.

### Reference

<?reference?>
