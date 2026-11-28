---
title: Scaling characters, quotients and extensions of Haar measure
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.Haar.NormedSpace
  - Mathlib.MeasureTheory.Measure.Haar.Disintegration
  - Mathlib.MeasureTheory.Measure.Haar.DistribChar
  - Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
  - Mathlib.MeasureTheory.Measure.Haar.Quotient
  - Mathlib.MeasureTheory.Measure.Haar.Extension
  - Mathlib.MeasureTheory.Measure.Lebesgue.Complex
  - Mathlib.MeasureTheory.Measure.Lebesgue.Integral
explains:
  E2: [MeasureTheory.Measure.integral_comp_smul, MeasureTheory.Measure.integral_comp_mul_left, MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable, LinearMap.exists_map_addHaar_eq_smul_addHaar, MeasureTheory.ae_comp_linearMap_mem_iff, MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul, MeasureTheory.mulEquivHaarChar_smul_map, MeasureTheory.integral_comap_eq_mulEquivHaarChar_smul, QuotientGroup.integral_eq_integral_automorphize, TopologicalGroup.IsSES.integral_inducedMeasure]
  E1: auto
families: []
requires: [V13, V16, V18.C02, V18.C03, V18.C05, V18.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Scaling characters, quotients and extensions of Haar measure

### Overview

A Haar measure is unique up to a positive constant. This simple fact has many consequences, and this section collects several of them. If $\varphi$ is a continuous automorphism of a locally compact group $G$, the image of a Haar measure under $\varphi$ is again a Haar measure, so it is a constant multiple of the first one. The constant is a scaling character of $\varphi$. On $\mathbb{R}^n$ the scaling $x \mapsto Rx$ multiplies the Lebesgue measure by $|R|^n$, which gives the change of variables formulas for integrals over dilations. For a surjective linear map $L$, the image of a Haar measure is a Haar measure, and almost every statement on the target pulls back to almost every statement on the source.

The section also explains how Haar measures pass to quotients $G/\Gamma$ by a discrete subgroup, and how they combine along a short exact sequence of groups $1 \to A \to B \to C \to 1$. It ends with some facts on the Lebesgue measure of $\mathbb{C}$ and of $\mathbb{R}$. The Haar measure and its uniqueness come from Chapter 3, Section 2, and the integral is the Bochner integral of Chapter 5.

### The library around it

#### Scaling in a normed space

The file `Mathlib.MeasureTheory.Measure.Haar.NormedSpace` gives the change of variables for dilations. Let $E$ be a finite dimensional real normed space with an additive Haar measure $\mu$, and let $n$ be its dimension. Then `MeasureTheory.Measure.integral_comp_smul` gives

$$\int_E f(Rx) \, d\mu(x) = |R^{-n}| \int_E f(x) \, d\mu(x)$$

for every real $R$. Related forms are `MeasureTheory.Measure.integral_comp_inv_smul` for $f(R^{-1}x)$ and `MeasureTheory.Measure.setIntegral_comp_smul_of_pos` for integrals over a set. On $\mathbb{R}$ itself, `MeasureTheory.Measure.integral_comp_mul_left` gives $\int g(ax) \, dx = |a^{-1}| \int g(y) \, dy$ and `MeasureTheory.Measure.integral_comp_div` gives $\int g(x/a) \, dx = |a| \int g(y) \, dy$. Integrability is kept by the scaling, `MeasureTheory.integrable_comp_smul_iff`, for $R \ne 0$.

The same file has a result on automatic continuity. A measurable additive map between normed groups, from a locally compact group into a real normed space, is continuous, `MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable`. The proof first shows that $f$ is bounded near $0$, `AddMonoidHom.exists_nhds_isBounded`, from a set of positive measure on which $f$ is bounded.

#### Surjective linear maps

The file `Mathlib.MeasureTheory.Measure.Haar.Disintegration` is about a surjective linear map $L : E \to F$ between finite dimensional spaces over a complete nontrivially normed field. Let $\mu$ and $\nu$ be additive Haar measures on $E$ and $F$. Then `LinearMap.exists_map_addHaar_eq_smul_addHaar` gives a constant $c > 0$ with $L_* \mu = c \, \nu$. The proof writes $E$ as $\ker L \times F'$ with $F'$ isomorphic to $F$, and uses that a product of Haar measures is a Haar measure.

The main application is `MeasureTheory.ae_comp_linearMap_mem_iff`: for a measurable set $s \subseteq F$,

$$(\forall^{\mu} x, \ L x \in s) \iff (\forall^{\nu} y, \ y \in s).$$

So almost everywhere statements on $F$ are almost everywhere statements on $E$. The lemma `MeasureTheory.ae_ae_add_linearMap_mem_iff` is a version with a second variable: for almost every $y$ and almost every $x$, $y + L x \in s$, if and only if almost every $y$ is in $s$.

#### Scaling characters

The file `Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar` attaches a number to each continuous automorphism $\varphi$ of a locally compact group $G$. The number `MeasureTheory.mulEquivHaarChar φ` is the constant $c$ with $c \, \varphi_* \mu = \mu$ for a regular Haar measure $\mu$, `MeasureTheory.mulEquivHaarChar_smul_map`. The type of $\varphi$ is `ContinuousMulEquiv G G`, with the notation `G ≃ₜ* G`. The constant does not depend on the choice of $\mu$, by uniqueness. It is positive, `MeasureTheory.mulEquivHaarChar_pos`, multiplicative, `MeasureTheory.mulEquivHaarChar_trans`, and $1$ on a compact group, `MeasureTheory.mulEquivHaarChar_eq_one_of_compactSpace`, because the total mass is finite and positive. For integrals, `MeasureTheory.integral_comap_eq_mulEquivHaarChar_smul` gives $\int f \, d(\varphi^* \mu) = c \int f \, d\mu$. The additive version is `MeasureTheory.addEquivAddHaarChar`.

The file `Mathlib.MeasureTheory.Measure.Haar.DistribChar` does the same for a group $G$ that acts on a locally compact additive group $A$ by additive maps. The map `MeasureTheory.distribHaarChar A` is a group homomorphism from $G$ to `NNReal`. Its value at $g$ is the scalar factor `MeasureTheory.Measure.addHaarScalarFactor` between the Haar measure and its image under $g$, `MeasureTheory.distribHaarChar_apply`. In practice it is computed on one set: `MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul` says that if $\mu(g s) = r \mu(s)$ for one set $s$ with $0 < \mu(s) < \infty$, then the character at $g$ is $r$. For the units of a local field acting on the field by multiplication, this character is the normalized absolute value.

#### Quotients by a discrete subgroup

The file `Mathlib.MeasureTheory.Measure.Haar.Quotient` treats a countable subgroup $\Gamma$ of a group $G$ with a fundamental domain $\mathcal{F}$ for the action of $\Gamma$ by right multiplication. The predicate is `MeasureTheory.IsFundamentalDomain`, and Section 2 treats it. A measure $\mu$ on $G/\Gamma$ agrees with the measure of preimages when $\mu(V) = \nu(\pi^{-1}(V) \cap \mathcal{F})$ for each measurable set $V$; this is the class `MeasureTheory.QuotientMeasureEqMeasurePreimage`. Then the projection $\pi$ is measure preserving from $\nu$ restricted to $\mathcal{F}$, `measurePreserving_quotientGroup_mk_of_QuotientMeasureEqMeasurePreimage`.

For a normal subgroup, the quotient measure of a left invariant measure is left invariant, `MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient`, and the quotient of a Haar measure with finite covolume is a Haar measure on $G/\Gamma$, `MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient`. The integration formula is `QuotientGroup.integral_eq_integral_automorphize`: for an integrable $f$ on $G$,

$$\int_G f \, d\nu = \int_{G/\Gamma} \sum_{\gamma \in \Gamma} f(x \gamma) \, d\mu(x).$$

The function $x \mapsto \sum_\gamma f(x\gamma)$ is `QuotientGroup.automorphize f`. The model case is $\mathbb{R} / \mathbb{Z}$ with the fundamental domain $[0, 1)$, where the formula says $\int_{\mathbb{R}} f = \int_0^1 \sum_n f(x + n) \, dx$.

#### Extensions

The file `Mathlib.MeasureTheory.Measure.Haar.Extension` builds a Haar measure on the middle group of a short exact sequence. The predicate `TopologicalGroup.IsSES φ ψ` says that $\varphi : A \to B$ and $\psi : B \to C$ form a short exact sequence of topological groups. With Haar measures $\mu_A$ on $A$ and $\mu_C$ on $C$, the map `TopologicalGroup.IsSES.integrate` sends a continuous function $f$ with compact support on $B$ to the double integral: first integrate $f$ over each coset of $\varphi(A)$ with $\mu_A$, then integrate the result over $C$ with $\mu_C$. This is a positive linear functional, so the Riesz-Markov-Kakutani theorem of Chapter 5 gives a measure `TopologicalGroup.IsSES.inducedMeasure`. The defining formula is `TopologicalGroup.IsSES.integral_inducedMeasure`, which says that the integral of $f$ for the induced measure is the double integral.

#### Lebesgue measure on the complex plane and on the line

The file `Mathlib.MeasureTheory.Measure.Lebesgue.Complex` identifies the volume of `ℂ` with the product of the volumes of the real and imaginary parts. The map `Complex.measurableEquivRealProd` is measure preserving, `Complex.volume_preserving_equiv_real_prod`, and so is `Complex.measurableEquivPi`, `Complex.volume_preserving_equiv_pi`.

The file `Mathlib.MeasureTheory.Measure.Lebesgue.Integral` has some facts on integrals over $\mathbb{R}$. The area under a graph is an integral: for integrable $f \le g$ on $s$, `volume_regionBetween_eq_integral` gives the product measure of the region between the graphs as $\int_s (g - f)$. Reflection gives `integral_comp_neg_Ioi`, and `integral_comp_abs` gives $\int f(|x|) \, dx = 2 \int_0^\infty f(x) \, dx$. The lemma `Real.integrable_of_summable_norm_Icc` proves integrability of a continuous function from the summability of the sup norms on the intervals $[n, n+1]$.

#### Common errors

1. Using `MeasureTheory.mulEquivHaarChar_smul_map` without the class `MeasureTheory.Measure.Regular`. The uniqueness of Haar measure is proved for regular measures, and the lemma needs it. On a second countable group every Haar measure is regular, but in general this is a hypothesis.
2. Reading the factor in `MeasureTheory.Measure.integral_comp_smul` the wrong way. Substituting $Rx$ divides the integral by $|R|^n$; the factor is $|R^{-n}|$, not $|R|^n$. The lemma for $f(R^{-1} x)$ is `MeasureTheory.Measure.integral_comp_inv_smul`.
3. Forgetting the surjectivity hypothesis in `MeasureTheory.ae_comp_linearMap_mem_iff`. For the zero map $L$, the left side says only that $0 \in s$, and this says nothing about almost every $y$.

### Exercises

1. (A) Use `MeasureTheory.Measure.integral_comp_mul_left` to compute $\int_{\mathbb{R}} e^{-a^2 x^2} \, dx$ from $\int_{\mathbb{R}} e^{-x^2} \, dx = \sqrt{\pi}$, for $a \ne 0$.
2. (A) Compute `MeasureTheory.distribHaarChar ℝ` at a unit $u$ of $\mathbb{R}$ acting by multiplication, with `MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul` and the interval $[0, 1]$.
3. (B) Let $L : \mathbb{R}^2 \to \mathbb{R}$ be $(x, y) \mapsto x + y$. Use `MeasureTheory.ae_comp_linearMap_mem_iff` to show that for almost every $(x, y)$ the sum $x + y$ is irrational.
4. (B) Prove the formula of `QuotientGroup.integral_eq_integral_automorphize` for $G = \mathbb{R}$, $\Gamma = \mathbb{Z}$ and the fundamental domain $[0, 1)$, from the monotone convergence theorem.
5. (B) Show that the scaling character of the automorphism $x \mapsto 2x$ of $\mathbb{R}$ is $2$, and of the automorphism $x \mapsto -x$ is $1$.
6. (C) Prove `MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable` for additive maps $\mathbb{R} \to \mathbb{R}$. Use the Steinhaus theorem: for a set $A$ of positive measure, $A - A$ contains an interval around $0$.

### Reference

<?reference?>
