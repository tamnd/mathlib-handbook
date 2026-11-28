---
title: Composition, integrals and categories of kernels
kind: api
modules:
  - Mathlib.Probability.Kernel.Composition.CompNotation
  - Mathlib.Probability.Kernel.Composition.MeasureComp
  - Mathlib.Probability.Kernel.Composition.Lemmas
  - Mathlib.Probability.Kernel.Composition.IntegralCompProd
  - Mathlib.Probability.Kernel.Integral
  - Mathlib.Probability.Kernel.SetIntegral
  - Mathlib.Probability.Kernel.MeasurableIntegral
  - Mathlib.Probability.Kernel.MeasurableLIntegral
  - Mathlib.Probability.Kernel.CompProdEqIff
  - Mathlib.Probability.Kernel.Composition.ParallelComp
  - Mathlib.Probability.Kernel.Composition.KernelLemmas
  - Mathlib.Probability.Kernel.Deterministic
  - Mathlib.Probability.Kernel.Representation
  - Mathlib.Probability.Kernel.Category.SFinKer
  - Mathlib.Probability.Kernel.Category.Stoch
explains:
  E2: [MeasureTheory.Measure.comp_assoc, MeasureTheory.Measure.compProd_eq_comp_prod, ProbabilityTheory.integral_compProd, ProbabilityTheory.Kernel.compProd_eq_iff, ProbabilityTheory.Kernel.parallelComp, ProbabilityTheory.Kernel.parallelComp_apply, ProbabilityTheory.IsDeterministic, ProbabilityTheory.Kernel.isDeterministic_iff_isZeroOneMeasure, ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval, SFinKer]
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

## Composition, integrals and categories of kernels

### Overview

Section 1 defined kernels, their composition $\eta \circ \kappa$ and their composition-product $\kappa \otimes \eta$. This section collects the rest of the toolkit. It has five parts: the composition of a measure with a kernel, the integral against a composition-product, the measurability of integrals that depend on a parameter, the parallel composition of two kernels, and the deterministic kernels. The section ends with the two categories that Mathlib builds from kernels.

The composition of a measure $\mu$ on $\alpha$ with a kernel $\kappa$ from $\alpha$ to $\beta$ is the measure
$$(\kappa \circ \mu)(B) = \int \kappa(a)(B) \, d\mu(a).$$
If $\mu$ is the law of $X$ and $\kappa$ is the conditional law of $Y$ given $X$, then $\kappa \circ \mu$ is the law of $Y$. The composition-product $\mu \otimes \kappa$ is the joint law of $(X, Y)$, and the integral of $f$ against it is the iterated integral $\int \int f(a, b) \, d\kappa(a)(b) \, d\mu(a)$. This is the theorem of Fubini for kernels, and most proofs about kernels reduce to it.

A kernel is deterministic when it carries no randomness: each measure $\kappa(a)$ takes only the values $0$ and $1$. The Dirac kernel $a \mapsto \delta_{f(a)}$ of a measurable map is the basic example. In the other direction, each Markov kernel with values in a standard Borel space is the image of the uniform measure on $[0, 1]$ under a measurable map. So all the randomness of a kernel can be moved into one uniform variable.

### The library around it

#### The composition of a measure and a kernel

The notation `κ ∘ₘ μ` of `Mathlib.Probability.Kernel.Composition.CompNotation` stands for `MeasureTheory.Measure.bind` $\mu$ $\kappa$. The module defines no new operation. Its lemmas `MeasureTheory.Measure.comp_apply_univ`, `MeasureTheory.Measure.deterministic_comp_eq_map` and `MeasureTheory.Measure.const_comp` give the total mass, the composition with a Dirac kernel, which is the image measure, and the composition with a constant kernel.

The module `Mathlib.Probability.Kernel.Composition.MeasureComp` proves the algebra of the composition. The law `MeasureTheory.Measure.comp_assoc` is the associativity $\eta \circ (\kappa \circ \mu) = (\eta \circ \kappa) \circ \mu$. The composition is additive in both arguments and commutes with scalars. The theorem `MeasureTheory.Measure.ae_comp_iff` says that a property holds almost everywhere for $\kappa \circ \mu$ if and only if it holds $\kappa(a)$-almost everywhere for $\mu$-almost every $a$. The theorem `MeasureTheory.Measure.compProd_eq_comp_prod` writes the composition-product as a composition: $\mu \otimes \kappa = (\mathrm{id} \times \kappa) \circ \mu$. The lemmas `MeasureTheory.Measure.AbsolutelyContinuous.comp` and its two one sided forms show that the composition preserves absolute continuity.

#### Integrals against a composition-product

The module `Mathlib.Probability.Kernel.Composition.IntegralCompProd` proves the theorem of Fubini for kernels. The criterion `ProbabilityTheory.integrable_compProd_iff` says that $f$ is integrable for $(\kappa \otimes \eta)(a)$ if and only if $f(b, \cdot)$ is integrable for $\eta(a, b)$ for almost every $b$ and the integral of its norm is integrable. The formula is `ProbabilityTheory.integral_compProd`:
$$\int f \, d(\kappa \otimes \eta)(a) = \int \int f(b, c) \, d\eta(a, b)(c) \, d\kappa(a)(b).$$
The same module proves the version for the composition $\eta \circ \kappa$, the set integral versions, and the forms for a measure, such as `MeasureTheory.Measure.integral_compProd`. The module `Mathlib.Probability.Kernel.Integral` computes the integral against the simple kernels: `ProbabilityTheory.Kernel.integral_deterministic` gives $\int g \, d\delta_{f(a)} = g(f(a))$, and there are lemmas for the constant, restricted and piecewise kernels. The single lemma of `Mathlib.Probability.Kernel.SetIntegral` is `ProbabilityTheory.Kernel.integral_integral_indicator`.

#### Measurability of integrals with a parameter

A composition needs $a \mapsto \int f(a, b) \, d\kappa(a)(b)$ to be measurable. The module `Mathlib.Probability.Kernel.MeasurableLIntegral` proves it for the lower integral of a measurable function with values in $[0, \infty]$, in `Measurable.lintegral_kernel_prod_right` and its variants, and `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left` is the case of an indicator. The module `Mathlib.Probability.Kernel.MeasurableIntegral` proves strong measurability for the Bochner integral, in `MeasureTheory.StronglyMeasurable.integral_kernel_prod_right` and its variants, and shows that the set of parameters where the function is integrable is measurable.

#### Equality almost everywhere

The theorem `ProbabilityTheory.Kernel.compProd_eq_iff` says that $\mu \otimes \kappa = \mu \otimes \eta$ if and only if $\kappa = \eta$ for $\mu$-almost every point, for finite kernels and a finite measure. It needs $\alpha$ countable or the $\sigma$-algebra of $\beta$ countably generated. This is the uniqueness statement behind the disintegration of Section 2: a conditional kernel is unique up to a null set.

#### Parallel composition

The kernel `ProbabilityTheory.Kernel.parallelComp` $\kappa$ $\eta$, with the notation `κ ∥ₖ η`, runs two kernels side by side. It goes from $\alpha \times \gamma$ to $\beta \times \delta$, and `ProbabilityTheory.Kernel.parallelComp_apply` gives $(\kappa \parallel \eta)(a, c) = \kappa(a) \times \eta(c)$. The definition needs s-finite kernels, and it takes the value $0$ otherwise. The module `Mathlib.Probability.Kernel.Composition.KernelLemmas` proves the interchange law `ProbabilityTheory.Kernel.parallelComp_comp_parallelComp`, $(\eta_1 \parallel \eta_2) \circ (\kappa_1 \parallel \kappa_2) = (\eta_1 \circ \kappa_1) \parallel (\eta_2 \circ \kappa_2)$, and the symmetry `ProbabilityTheory.Kernel.swap_parallelComp`. With the copy kernel $a \mapsto \delta_{(a, a)}$, the module `Mathlib.Probability.Kernel.Composition.Lemmas` writes a composition-product as a copy followed by a parallel composition, in `MeasureTheory.Measure.compProd_eq_parallelComp_comp_copy_comp`.

#### Deterministic kernels and representation

The class `ProbabilityTheory.IsDeterministic` $\kappa$ says that copying the input and then applying $\kappa$ to both copies gives the same result as applying $\kappa$ and then copying the output. This is the definition of a deterministic map in a Markov category. The theorem `ProbabilityTheory.Kernel.isDeterministic_iff_isZeroOneMeasure` connects it with the measure theoretic notion: a finite kernel is deterministic if and only if each $\kappa(a)$ takes only the values $0$ and $1$. On a standard Borel space, `ProbabilityTheory.Kernel.IsDeterministic.exists_eq_deterministic` says that a deterministic Markov kernel is the Dirac kernel of a measurable map. The Dirac kernels, the identity, the copy, the discard and the swap kernels are deterministic by instances.

The module `Mathlib.Probability.Kernel.Representation` proves `ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval`. For a Markov kernel $\kappa$ with values in a standard Borel space, there is a jointly measurable $f : \alpha \to [0, 1] \to \beta$ such that $\kappa(a)$ is the image of the Lebesgue measure under $f(a)$. The special case `MeasureTheory.Measure.exists_measurable_map_eq` is the statement for one probability measure.

#### Categories of kernels

The module `Mathlib.Probability.Kernel.Category.SFinKer` defines the category `SFinKer`. Its objects are measurable spaces and its morphisms are s-finite kernels, with the composition of kernels. The product of measurable spaces and the parallel composition make it a symmetric monoidal category, and the copy and discard kernels make each object a comonoid. So `SFinKer` is a copy-discard category, by the instance `SFinKer.instCopyDiscardCategory`. The module `Mathlib.Probability.Kernel.Category.Stoch` defines `Stoch` as the wide subcategory of Markov kernels. It is a positive Markov category, by `instPositiveCategoryStoch`. The positivity equation is `ProbabilityTheory.Kernel.comp_parallelComp_comp_copy`, which holds for Markov kernels and fails for s-finite ones.

#### Common errors

1. The composition `κ ∘ₘ μ` is notation for `MeasureTheory.Measure.bind`, so a search for lemmas must use both names. A goal stated with `MeasureTheory.Measure.bind` matches the lemmas of this section only after a rewrite.
2. The parallel composition and the composition-product of a kernel that is not s-finite are $0$ by definition. A lemma about them needs the instance `ProbabilityTheory.IsSFiniteKernel`, and a missing instance makes the statement true for the wrong reason.
3. The criterion `ProbabilityTheory.Kernel.compProd_eq_iff` needs a countability hypothesis on $\alpha$ or on the $\sigma$-algebra of $\beta$. On general spaces the conclusion can fail.

### Exercises

1. (A) Show that $\delta_{f} \circ \mu$ is the image measure $f_* \mu$, and that the composition of $\mu$ with the constant kernel $\nu$ is $\mu(\alpha) \, \nu$.
2. (A) Show that the total mass of $\kappa \circ \mu$ is $\mu(\alpha)$ when $\kappa$ is a Markov kernel.
3. (B) Prove that $\mu \otimes \kappa = (\mathrm{id} \times \kappa) \circ \mu$, and deduce the integral formula for $\mu \otimes \kappa$ from the formula for compositions.
4. (B) Show that a kernel $\kappa$ with $\kappa(a) \in \{0, \delta_{b}\}$ for each $a$ is deterministic in the sense of copying.
5. (B) Show that the interchange law for parallel composition follows from the formula for the product of two measures on rectangles.
6. (C) Let $F$ be a distribution function on $\mathbb{R}$ and $F^{-1}(u) = \inf \{x : F(x) \ge u\}$. Show that the image of the Lebesgue measure on $[0, 1]$ under $F^{-1}$ has the distribution function $F$. This is the real case of the representation theorem.

### Reference

<?reference?>
