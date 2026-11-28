---
title: Kernels with density and Radon-Nikodym derivatives of kernels
kind: api
modules:
  - Mathlib.Probability.Kernel.WithDensity
  - Mathlib.Probability.Kernel.Composition.WithDensity
  - Mathlib.Probability.Kernel.RadonNikodym
  - Mathlib.Probability.Kernel.Composition.RadonNikodym
  - Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
explains:
  E2: [ProbabilityTheory.Kernel.withDensity, ProbabilityTheory.Kernel.withDensity_apply, ProbabilityTheory.Kernel.rnDeriv, ProbabilityTheory.Kernel.singularPart, ProbabilityTheory.Kernel.rnDeriv_add_singularPart, ProbabilityTheory.Kernel.mutuallySingular_singularPart, ProbabilityTheory.Kernel.singularPart_eq_zero_iff_absolutelyContinuous, ProbabilityTheory.rnDeriv_measure_compProd, MeasureTheory.Measure.absolutelyContinuous_compProd_iff']
  E1: auto
families: []
requires: [V18, V20.C01, V20.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Kernels with density and Radon-Nikodym derivatives of kernels

### Overview

A measure $\mu$ with a density $f$ is the measure $f \cdot \mu$ with $(f \cdot \mu)(B) = \int_B f \, d\mu$. The theorem of Radon and Nikodym goes in the other direction. Each $\sigma$-finite measure $\mu$ splits as $\mu = f \cdot \nu + \mu_s$, where $f$ is the Radon-Nikodym derivative $d\mu / d\nu$ and $\mu_s$ is singular with respect to $\nu$. This section describes the same two constructions for kernels.

For kernels, the density is a function $f(a, b)$ of two variables. The kernel $f \cdot \kappa$ sends $a$ to the measure $f(a, \cdot) \cdot \kappa(a)$. The construction is direct, and the only work is to show that the result is again a kernel, that is, measurable in $a$.

The Radon-Nikodym derivative of a kernel is harder. For each $a$, the measure $\kappa(a)$ has a derivative $d\kappa(a)/d\eta(a)$, but the theorem for measures gives this function only up to a null set, and with no control in $a$. A choice for each $a$ separately need not be measurable in the pair $(a, b)$. Mathlib solves this with a martingale argument. It builds a jointly measurable function $\mathrm{rnDeriv}(\kappa, \eta)$ such that, for each $a$,
$$\kappa(a) = \mathrm{rnDeriv}(\kappa, \eta)(a, \cdot) \cdot \eta(a) + \mathrm{singularPart}(\kappa, \eta)(a),$$
and the second term is singular with respect to $\eta(a)$. The construction needs a countability hypothesis: the space $\alpha$ is countable, or the $\sigma$-algebra of the target $\gamma$ is countably generated.

The last two modules connect these objects with the composition-product of Section 1. The derivative of $\mu \otimes \kappa$ with respect to $\nu \otimes \eta$ is the product of the derivative of $\mu$ with respect to $\nu$ and the derivative of $\kappa$ with respect to $\eta$. This chain rule is the basis of the chain rule for the Kullback-Leibler divergence and for other $f$-divergences.

### The library around it

#### Kernels with density

The kernel `ProbabilityTheory.Kernel.withDensity` $\kappa$ $f$ takes a kernel $\kappa$ from $\alpha$ to $\beta$ and a function $f : \alpha \to \beta \to [0, \infty]$. It is defined when $\kappa$ is s-finite and $f$ is measurable as a function of the pair, and it is $0$ otherwise. The theorem `ProbabilityTheory.Kernel.withDensity_apply` computes its value: $(f \cdot \kappa)(a)$ is the measure `MeasureTheory.Measure.withDensity` of $\kappa(a)$ and $f(a, \cdot)$. The theorems `ProbabilityTheory.Kernel.lintegral_withDensity` and `ProbabilityTheory.Kernel.integral_withDensity` give the integrals: $\int g \, d(f \cdot \kappa)(a) = \int f(a, b) g(b) \, d\kappa(a)(b)$.

The result is finite when the density is bounded, by `ProbabilityTheory.Kernel.isFiniteKernel_withDensity_of_bounded`. A kernel with an unbounded density can fail to be finite even when $\kappa$ is a Markov kernel. The result is s-finite when the density takes only finite values, by `ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity`, and an instance covers densities with values in $[0, \infty)$. The proof writes the density as a countable sum of bounded functions and uses `ProbabilityTheory.Kernel.withDensity_tsum`, which says that the construction commutes with countable sums. The construction is also additive in the density, by `ProbabilityTheory.Kernel.withDensity_add_left`, and `ProbabilityTheory.Kernel.withDensity_one` gives $1 \cdot \kappa = \kappa$.

The module `Mathlib.Probability.Kernel.Composition.WithDensity` relates the density with the composition-product. The theorems `ProbabilityTheory.Kernel.compProd_withDensity` and `MeasureTheory.Measure.compProd_withDensity` say that a density on the second kernel becomes a density on the product: $\mu \otimes (f \cdot \kappa) = f \cdot (\mu \otimes \kappa)$. The theorems `MeasureTheory.Measure.withDensity_comp` and `ProbabilityTheory.Kernel.withDensity_comp_left` treat the composition in the same way.

#### The Radon-Nikodym derivative of a kernel

The module `Mathlib.Probability.Kernel.RadonNikodym` defines `ProbabilityTheory.Kernel.rnDeriv` $\kappa$ $\eta$ and `ProbabilityTheory.Kernel.singularPart` $\kappa$ $\eta$ for two finite kernels from $\alpha$ to $\gamma$. The hypothesis is `MeasurableSpace.CountableOrCountablyGenerated` $\alpha$ $\gamma$, which holds when $\alpha$ is countable or when the $\sigma$-algebra of $\gamma$ is countably generated, for example on a standard Borel space.

The construction uses the density of Section 6 with respect to the sum $\kappa + \eta$. The density $g$ of $\kappa$ with respect to $\kappa + \eta$ takes values in $[0, 1]$. Then $\mathrm{rnDeriv}(\kappa, \eta) = g / (1 - g)$, and the singular part is the part of $\kappa$ that lives on the set where $g = 1$. The function is measurable in the pair by `ProbabilityTheory.Kernel.measurable_rnDeriv`.

The main theorem is the decomposition `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`:
$$\eta.\mathrm{withDensity}(\mathrm{rnDeriv}(\kappa, \eta)) + \mathrm{singularPart}(\kappa, \eta) = \kappa.$$
The theorem `ProbabilityTheory.Kernel.mutuallySingular_singularPart` says that $\mathrm{singularPart}(\kappa, \eta)(a)$ and $\eta(a)$ are mutually singular for each $a$. So the decomposition is the Lebesgue decomposition of each measure $\kappa(a)$, but with a choice that is measurable in $a$. The theorem `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure` says that $\mathrm{rnDeriv}(\kappa, \eta)(a, \cdot)$ is equal $\eta(a)$-almost everywhere to the derivative `MeasureTheory.Measure.rnDeriv` of the two measures. So each lemma about the derivative of measures transfers to kernels, one point $a$ at a time.

Two theorems characterize the extreme cases. The theorem `ProbabilityTheory.Kernel.singularPart_eq_zero_iff_absolutelyContinuous` says that the singular part at $a$ is $0$ if and only if $\kappa(a) \ll \eta(a)$. The theorem `ProbabilityTheory.Kernel.withDensity_rnDeriv_eq_zero_iff_mutuallySingular` says that the absolutely continuous part at $a$ is $0$ if and only if $\kappa(a)$ and $\eta(a)$ are mutually singular. The sets of $a$ where these properties hold are measurable, by `ProbabilityTheory.Kernel.measurableSet_absolutelyContinuous` and `ProbabilityTheory.Kernel.measurableSet_mutuallySingular`. These measurability facts are not obvious, and they need the joint measurability of the derivative.

#### Derivatives of composition-products

The module `Mathlib.Probability.Kernel.Composition.RadonNikodym` proves the chain rule. The theorem `ProbabilityTheory.rnDeriv_measure_compProd` says that, for finite measures $\mu$, $\nu$ and Markov kernels $\kappa$, $\eta$,
$$\frac{d(\mu \otimes \kappa)}{d(\nu \otimes \eta)}(a, b) = \frac{d\mu}{d\nu}(a) \, \frac{d\kappa}{d\eta}(a, b)$$
for $(\nu \otimes \eta)$-almost every $(a, b)$. The theorems `ProbabilityTheory.rnDeriv_measure_compProd_left` and `ProbabilityTheory.rnDeriv_measure_compProd_right` treat the cases where only one factor changes. The theorem `ProbabilityTheory.rnDeriv_compProd` is the version for kernels.

The module `Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous` gives the criterion for absolute continuity. The theorem `MeasureTheory.Measure.absolutelyContinuous_compProd_iff'` says that $\mu \otimes \kappa \ll \nu \otimes \eta$ if and only if $\mu \ll \nu$ and $\kappa(a) \ll \eta(a)$ for $\mu$-almost every $a$. The theorem `MeasureTheory.Measure.absolutelyContinuous_compProd_right_iff` is the case $\mu = \nu$. The theorem `MeasureTheory.Measure.mutuallySingular_compProd_right_iff` gives the criterion for mutual singularity, and `MeasureTheory.Measure.AbsolutelyContinuous.kernel_of_compProd` extracts the condition on the kernels.

#### Common errors

1. The kernel `ProbabilityTheory.Kernel.withDensity` is $0$ when the density is not measurable as a function of the pair. A proof that unfolds it must give the measurability, and a function that is measurable in $b$ for each fixed $a$ is not enough.
2. The derivative `ProbabilityTheory.Kernel.rnDeriv` needs the instance `MeasurableSpace.CountableOrCountablyGenerated`. On a general target space no jointly measurable choice need exist, and the lemmas do not apply.
3. The equality of `ProbabilityTheory.Kernel.rnDeriv` with the derivative of measures holds only almost everywhere for each $a$. A rewrite inside an integral needs the almost everywhere form, and not an equality of functions.

### Exercises

1. (A) Show that $\kappa.\mathrm{withDensity}(1) = \kappa$ for an s-finite kernel $\kappa$, and that the density $f + g$ gives the sum of the two kernels with density.
2. (A) Let $\kappa$ be a Markov kernel and $f$ a measurable density bounded by $C$. Show that $(f \cdot \kappa)(a)(\beta) \le C$ for each $a$.
3. (B) Show that $\mathrm{singularPart}(\kappa, \eta) = 0$ when $\kappa(a) \ll \eta(a)$ for all $a$, and deduce that $\kappa = \eta.\mathrm{withDensity}(\mathrm{rnDeriv}(\kappa, \eta))$ in this case.
4. (B) Let $\alpha$ be countable. Show directly that a choice of $d\kappa(a)/d\eta(a)$ for each $a$ gives a jointly measurable function. Explain why the argument fails for an uncountable $\alpha$.
5. (B) Prove the chain rule $d(\mu \otimes \kappa)/d(\nu \otimes \eta) = (d\mu/d\nu)(d\kappa/d\eta)$ when $\mu \ll \nu$ and $\kappa(a) \ll \eta(a)$ for all $a$, with the integral formula for the composition-product.
6. (C) Deduce from the chain rule that the Kullback-Leibler divergence satisfies $\mathrm{KL}(\mu \otimes \kappa \parallel \nu \otimes \eta) = \mathrm{KL}(\mu \parallel \nu) + \int \mathrm{KL}(\kappa(a) \parallel \eta(a)) \, d\mu(a)$ when all the divergences are finite.

### Reference

<?reference?>
