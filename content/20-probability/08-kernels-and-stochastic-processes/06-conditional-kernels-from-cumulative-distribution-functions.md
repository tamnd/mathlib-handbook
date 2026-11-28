---
title: Conditional kernels from cumulative distribution functions
kind: api
modules:
  - Mathlib.Probability.Kernel.Disintegration.MeasurableStieltjes
  - Mathlib.Probability.Kernel.Disintegration.CDFToKernel
  - Mathlib.Probability.Kernel.Disintegration.Density
explains:
  E2: [ProbabilityTheory.IsRatStieltjesPoint, ProbabilityTheory.IsMeasurableRatCDF, ProbabilityTheory.stieltjesOfMeasurableRat, ProbabilityTheory.IsCondKernelCDF, ProbabilityTheory.IsCondKernelCDF.toKernel, ProbabilityTheory.compProd_toKernel, ProbabilityTheory.IsRatCondKernelCDF, ProbabilityTheory.Kernel.density, ProbabilityTheory.Kernel.setIntegral_density, ProbabilityTheory.Kernel.martingale_densityProcess]
  E1: auto
families: []
requires: [V18, V20.C01, V20.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Conditional kernels from cumulative distribution functions

### Overview

Section 2 stated the disintegration theorem. For a kernel $\kappa$ from $\alpha$ to $\beta \times \Omega$, with $\Omega$ a standard Borel space, there is a kernel $\eta$ from $\alpha \times \beta$ to $\Omega$ such that $\kappa = \kappa_1 \otimes \eta$, where $\kappa_1$ is the first marginal. This section describes the three modules that do the main work of the proof. They are technical, but they contain constructions that are useful on their own.

The proof reduces to the case $\Omega = \mathbb{R}$, and on $\mathbb{R}$ a probability measure is given by its cumulative distribution function. So the task is to build a function $F(a, b, x)$ such that, for each $(a, b)$, the function $x \mapsto F(a, b, x)$ is a distribution function, and the joint law satisfies
$$\int_{s} F(a, b, x) \, d\kappa_1(a)(b) = \kappa(a)(s \times (-\infty, x]).$$
The difficulty is measurability. The equation for a fixed $x$ determines $F(a, \cdot, x)$ only up to a null set, and the null set depends on $x$. There are uncountably many values of $x$, so the union of the null sets can be large.

The solution has two steps. First, work with rational $x$ only. A countable union of null sets is null, so the properties of a distribution function hold for all rational $x$ at once, outside one null set. Second, extend from $\mathbb{Q}$ to $\mathbb{R}$ by right limits, and replace the function by a default distribution function on the exceptional set. The module `Mathlib.Probability.Kernel.Disintegration.MeasurableStieltjes` does the second step in a measurable way. The module `Mathlib.Probability.Kernel.Disintegration.CDFToKernel` turns the result into a kernel. The module `Mathlib.Probability.Kernel.Disintegration.Density` gives the first step on a general space, with a martingale.

### The library around it

#### Measurable families of distribution functions on the rationals

A point $a$ is a Stieltjes point of $f : \alpha \to \mathbb{Q} \to \mathbb{R}$ when $f(a)$ is monotone, tends to $0$ at $-\infty$ and to $1$ at $+\infty$, and is right continuous in the rational sense: $\inf_{r > t} f(a, r) = f(a, t)$ for each rational $t$. The structure `ProbabilityTheory.IsRatStieltjesPoint` records these four properties. The set of Stieltjes points of a measurable $f$ is measurable, by `ProbabilityTheory.measurableSet_isRatStieltjesPoint`.

The structure `ProbabilityTheory.IsMeasurableRatCDF` $f$ asks that each point is a Stieltjes point and that $f$ is measurable. For such an $f$, the definition `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction` extends $f(a)$ to a `StieltjesFunction` on $\mathbb{R}$ by $F(a, x) = \inf_{r > x} f(a, r)$. The theorem `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_eq` says that the extension agrees with $f$ on $\mathbb{Q}$, and `ProbabilityTheory.IsMeasurableRatCDF.measurable_stieltjesFunction` says that $a \mapsto F(a, x)$ is measurable for each real $x$.

A general measurable $f$ has Stieltjes points and other points. The function `ProbabilityTheory.defaultRatCDF` is the distribution function of the Dirac mass at $0$, restricted to $\mathbb{Q}$. The function `ProbabilityTheory.toRatCDF` $f$ replaces $f(a)$ by this default at each point $a$ that is not a Stieltjes point, and `ProbabilityTheory.isMeasurableRatCDF_toRatCDF` shows that the result has the property `ProbabilityTheory.IsMeasurableRatCDF`. The composite of the two steps is `ProbabilityTheory.stieltjesOfMeasurableRat` $f$, a function $\alpha \to$ `StieltjesFunction` that is defined for each measurable $f$. Its measurability is `ProbabilityTheory.measurable_stieltjesOfMeasurableRat`. The theorem `ProbabilityTheory.measure_stieltjesOfMeasurableRat_Iic` says that the measure of the Stieltjes function gives the half line $(-\infty, x]$ the mass $F(a, x)$, and `ProbabilityTheory.measure_stieltjesOfMeasurableRat_univ` says that the measure is a probability measure.

#### From a conditional distribution function to a kernel

Let $\kappa$ be a finite kernel from $\alpha$ to $\beta \times \mathbb{R}$ and $\nu$ a kernel from $\alpha$ to $\beta$. The structure `ProbabilityTheory.IsCondKernelCDF` $f$ $\kappa$ $\nu$ says that $f : \alpha \times \beta \to$ `StieltjesFunction` is measurable, tends to $0$ and $1$ at the two ends, is integrable in $b$, and satisfies
$$\int_{s} f(a, b)(x) \, d\nu(a)(b) = \kappa(a)(s \times (-\infty, x])$$
for each measurable set $s$ and each real $x$. From such an $f$, the definition `ProbabilityTheory.IsCondKernelCDF.toKernel` builds a Markov kernel from $\alpha \times \beta$ to $\mathbb{R}$. Its value at $p$ is the measure of the Stieltjes function $f(p)$, so `ProbabilityTheory.IsCondKernelCDF.toKernel_Iic` gives the mass $f(p)(x)$ to the half line $(-\infty, x]$. The main theorem is `ProbabilityTheory.compProd_toKernel`: $\nu \otimes \mathrm{toKernel}(f) = \kappa$. Its proof extends the equation from the rectangles $s \times (-\infty, x]$ to all measurable sets with the $\pi$-$\lambda$ theorem.

The structure `ProbabilityTheory.IsRatCondKernelCDF` is the rational version. It asks the integral equation only for rational $x$, and the Stieltjes properties only for $\nu(a)$-almost every $b$. These are the hypotheses that a construction with null sets can check. The theorem `ProbabilityTheory.isCondKernelCDF_stieltjesOfMeasurableRat` closes the gap: if $f$ has the rational property, then `ProbabilityTheory.stieltjesOfMeasurableRat` $f$ has the real property. The chain from a rational family to a kernel is thus complete.

#### The density of a kernel

The module `Mathlib.Probability.Kernel.Disintegration.Density` builds the rational family. Let $\kappa$ be a finite kernel from $\alpha$ to $\gamma \times \beta$ and $\nu$ a finite kernel from $\alpha$ to $\gamma$ with $\kappa_1 \le \nu$, where the $\sigma$-algebra of $\gamma$ is countably generated. The function `ProbabilityTheory.Kernel.density` $\kappa$ $\nu$ $a$ $x$ $s$ is a real number in $[0, 1]$, by `ProbabilityTheory.Kernel.density_nonneg` and `ProbabilityTheory.Kernel.density_le_one`. The main theorem is `ProbabilityTheory.Kernel.setIntegral_density`:
$$\int_{A} \mathrm{density}(\kappa, \nu)(a, x, s) \, d\nu(a)(x) = \kappa(a)(A \times s)$$
for measurable sets $A$ and $s$. The function is measurable in the pair $(a, x)$, by `ProbabilityTheory.Kernel.measurable_density`. This joint measurability is the point of the construction: the Radon-Nikodym theorem for one measure gives the density for each $a$, but with no control in $a$.

The construction uses a filtration from Section 1 of Chapter 7. Since $\gamma$ is countably generated, there is a sequence of finite partitions of $\gamma$, each finer than the one before, that generates the $\sigma$-algebra. The function `ProbabilityTheory.Kernel.densityProcess` at level $n$ is the ratio $\kappa(a)(P \times s) / \nu(a)(P)$, where $P$ is the cell of the $n$-th partition that contains $x$. It is a simple function of $x$, and it is clearly measurable in $(a, x)$. The theorem `ProbabilityTheory.Kernel.martingale_densityProcess` says that it is a martingale for $\nu(a)$ and this filtration. It is bounded by $1$, so the martingale convergence theorem of Chapter 7 gives a limit, by `ProbabilityTheory.Kernel.tendsto_densityProcess_limitProcess`. The density is this limit, and `ProbabilityTheory.Kernel.density_ae_eq_limitProcess` connects the two.

The density has two applications. With $\beta = \mathbb{R}$ and the sets $s = (-\infty, q]$ for rational $q$, it gives a family that has the property `ProbabilityTheory.IsRatCondKernelCDF`, and the disintegration of Section 2 follows. With $\beta$ a point, it gives a jointly measurable density of $\kappa$ with respect to $\nu$, and Section 5 uses it to build the Radon-Nikodym derivative of kernels.

#### Common errors

1. A `ProbabilityTheory.IsRatStieltjesPoint` asks for right continuity on $\mathbb{Q}$ in the form $\inf_{r > t} f(a, r) = f(a, t)$. Monotonicity and the limits at the two ends are not enough, and a proof that omits this field fails.
2. The function `ProbabilityTheory.stieltjesOfMeasurableRat` $f$ is equal to $f$ only at the Stieltjes points. At the other points it is the default function, so a lemma that evaluates it needs the hypothesis that the point is a Stieltjes point, or an almost everywhere statement.
3. The density `ProbabilityTheory.Kernel.density` needs the hypothesis $\kappa_1 \le \nu$ for most of its lemmas. Without it the values need not lie in $[0, 1]$ and the integral formula fails. The kernel $\nu = \kappa_1$ always satisfies it.

### Exercises

1. (A) Show that `ProbabilityTheory.defaultRatCDF` is monotone, tends to $0$ at $-\infty$ and to $1$ at $+\infty$, and satisfies the rational right continuity.
2. (A) Let $f : \mathbb{Q} \to \mathbb{R}$ be monotone and $F(x) = \inf_{r > x} f(r)$. Show that $F$ is monotone and right continuous on $\mathbb{R}$.
3. (B) Show that the set of Stieltjes points of a measurable $f : \alpha \to \mathbb{Q} \to \mathbb{R}$ is measurable. Use only countable operations on the values $f(a, q)$.
4. (B) Let $\gamma = [0, 1)$ with the dyadic partitions. Compute the density process of $\kappa$ with respect to $\nu$ when $\kappa(a) = \nu(a) \otimes \mu$ for a fixed probability measure $\mu$, and show that the density is $\mu(s)$.
5. (B) Prove that the density process is a martingale: the integral of the level $n + 1$ function over a cell of level $n$ is the integral of the level $n$ function.
6. (C) Let $\kappa$ be a Markov kernel from $\alpha$ to $\beta \times \mathbb{R}$. Combine the density with $s = (-\infty, q]$ and the theorem `ProbabilityTheory.isCondKernelCDF_stieltjesOfMeasurableRat` to build a kernel $\eta$ with $\kappa = \kappa_1 \otimes \eta$. Find the place where the countable generation of $\beta$ is used.

### Reference

<?reference?>
