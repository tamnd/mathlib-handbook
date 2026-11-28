---
title: Invariant measures and invariant integrals
kind: api
modules:
  - Mathlib.MeasureTheory.Group.Action
  - Mathlib.MeasureTheory.Group.AEStabilizer
  - Mathlib.MeasureTheory.Group.ModularCharacter
  - Mathlib.MeasureTheory.Group.Circle
  - Mathlib.MeasureTheory.Group.AddCircle
  - Mathlib.MeasureTheory.Group.Integral
  - Mathlib.MeasureTheory.Group.LIntegral
  - Mathlib.MeasureTheory.Group.Prod
explains:
  E2: [MeasureTheory.smulInvariantMeasure_tfae, MeasureTheory.measure_smul, MeasureTheory.measurePreserving_smul, MulAction.aestabilizer, MeasureTheory.integral_mul_left_eq_self, MeasureTheory.lintegral_mul_left_eq_self, MeasureTheory.measurePreserving_prod_mul, MeasureTheory.measure_mul_measure_eq, MeasureTheory.absolutelyContinuous_of_isMulLeftInvariant, MeasureTheory.Measure.modularCharacter]
  E1: auto
families: []
requires: [V13, V18.C02, V18.C03, V18.C04, V18.C05, V18.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Invariant measures and invariant integrals

### Overview

Lebesgue measure on $\mathbb{R}^n$ does not change under translation. Haar measure on a locally compact group does not change under left multiplication. The counting measure on a set does not change under any permutation. These are three examples of one notion: a measure that is invariant under the action of a group. Chapter 3 constructed Haar measure and Lebesgue measure as examples. This section explains the general API: invariant measures for an action, the integrals that do not change under the action, and the product tricks that prove the uniqueness of Haar measure.

The classes come from the file `Mathlib.MeasureTheory.Group.Defs`. The class `MeasureTheory.SMulInvariantMeasure M α μ` says that $\mu(c^{-1} \cdot s) = \mu(s)$ for every $c$ in `M` and every measurable set. For a group acting on itself by left multiplication, the class `MeasureTheory.Measure.IsMulLeftInvariant μ` says that `map (g * ·) μ = μ`. The class `MeasureTheory.Measure.IsMulRightInvariant` is the version for right multiplication, and `MeasureTheory.Measure.IsInvInvariant` says that inversion preserves the measure. Each class has an additive twin with `Add` in the name, generated from the multiplicative one. Lebesgue measure is an instance of the additive classes.

The section needs measures and their images from Chapter 2, Haar measure from Chapter 3, the integrals of Chapters 4 and 5 and the product measures of Chapter 6.

### The library around it

#### Invariant measures for an action

The file `Mathlib.MeasureTheory.Group.Action` gives the basic consequences of `SMulInvariantMeasure`. The class asks only for preimages of measurable sets, and `MeasureTheory.smulInvariantMeasure_tfae` lists equivalent forms. For a group `G` with a measurable action, the following are equivalent: the class holds; $\mu(c^{-1} \cdot s) = \mu(s)$ for measurable $s$; $\mu(c \cdot s) = \mu(s)$ for measurable $s$; the same two statements for all sets; `map (c • ·) μ = μ`; and the map `(c • ·)` is measure preserving.

The working lemmas are short:

| Lean name | Statement |
|---|---|
| `MeasureTheory.measure_smul` | $\mu(c \cdot s) = \mu(s)$ for every set $s$ |
| `MeasureTheory.measure_preimage_smul` | $\mu(c^{-1} \cdot s) = \mu(s)$ in the form of a preimage |
| `MeasureTheory.measurePreserving_smul` | the map $x \mapsto c \cdot x$ is measure preserving |
| `MeasureTheory.map_smul` | the image of $\mu$ under $x \mapsto c \cdot x$ is $\mu$ |
| `MeasureTheory.smul_ae` | the action of $c$ on the filter `ae μ` gives `ae μ` |
| `MeasureTheory.measure_smul_null` | the image of a null set is null |
| `MeasureTheory.smul_set_ae_eq` | $c \cdot s$ and $c \cdot t$ agree a.e. if and only if $s$ and $t$ agree a.e. |

The lemma `MeasureTheory.smulInvariantMeasure_map` transports invariance along an equivariant measurable map. The lemma `MeasureTheory.smulInvariantMeasure_iterateMulAct` relates the action of the iterates of one map $f$ to the statement that $f$ preserves the measure. Ergodic theory uses this case.

The same group can act on the measures themselves. Section 4 of Chapter 1 introduced the type `Gᵈᵐᵃ` and the formula `MeasureTheory.Measure.domSMul_apply`, $(g \cdot \mu)(s) = \mu(g^{-1} \cdot s)$. A measure is invariant exactly when it is a fixed point of this action. The lemma `MeasureTheory.integral_domSMul` gives the integral against $g \cdot \mu$ as the integral of a translated function against $\mu$.

#### Minimal actions

An action is minimal when every orbit is dense, for example the action of a group on itself. For a minimal continuous action, an invariant measure behaves like Haar measure. The lemma `MeasureTheory.measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero` says that if one compact set has positive measure, then every nonempty open set has positive measure. The proof covers the compact set by finitely many translates of the open set. The lemma `MeasureTheory.measure_pos_iff_nonempty_of_smulInvariant` gives the same for a regular measure that is not zero. In the other direction, `MeasureTheory.isLocallyFiniteMeasure_of_smulInvariant` says that one nonempty open set of finite measure makes the measure locally finite.

#### The almost everywhere stabilizer

For an invariant measure and a set $s$, the subgroup `MulAction.aestabilizer G μ s` contains the elements $g$ with $g \cdot s = s$ almost everywhere. This is the content of `MulAction.mem_aestabilizer`. It contains the ordinary stabilizer, by `MulAction.stabilizer_le_aestabilizer`. If $s$ is null or conull, the stabilizer is the whole group, by `MulAction.aestabilizer_of_eventuallyEmptyOrUniv`. Ergodic theory uses this subgroup. An action is ergodic when every set with a dense almost everywhere stabilizer is null or conull. The lemma `MeasureTheory.smul_ae_eq_self_of_mem_zpowers` says that if $x \cdot s = s$ almost everywhere, then the same holds for every power of $x$.

#### Integrals that do not change

The files `Mathlib.MeasureTheory.Group.Integral` and `Mathlib.MeasureTheory.Group.LIntegral` give the change of variables for translations. For a left invariant measure,
$$\int f(g x) \, d\mu(x) = \int f(x) \, d\mu(x).$$
This is `MeasureTheory.integral_mul_left_eq_self` for the Bochner integral and `MeasureTheory.lintegral_mul_left_eq_self` for the lower integral. The right versions are `MeasureTheory.integral_mul_right_eq_self` and `MeasureTheory.lintegral_mul_right_eq_self`. Inversion gives `MeasureTheory.integral_inv_eq_self`, and division gives `MeasureTheory.integral_div_left_eq_self` and `MeasureTheory.integral_div_right_eq_self`. For a general action, `MeasureTheory.integral_smul_eq_self` is the version with $f(g \cdot x)$.

For Lebesgue measure, these lemmas have additive names, for example `MeasureTheory.integral_add_left_eq_self`. They are the reason why $\int_{\mathbb{R}} f(x + a) \, dx = \int_{\mathbb{R}} f(x) \, dx$ needs no computation.

Integrability transfers in the same way: `MeasureTheory.Integrable.comp_mul_left`, `MeasureTheory.Integrable.comp_mul_right`, `MeasureTheory.Integrable.comp_inv` and `MeasureTheory.Integrable.comp_div_left`. On an ordered group, `MeasureTheory.IntegrableOn.comp_inv_Ioi` and its three siblings move a half line through the inversion.

A positive left invariant measure detects continuous functions that are not zero. The lemma `MeasureTheory.lintegral_eq_zero_of_isMulLeftInvariant` says that the lower integral of a continuous function with values in $[0, \infty]$ is zero if and only if the function is zero, for a regular left invariant measure that is not zero.

#### Product tricks

The file `Mathlib.MeasureTheory.Group.Prod` combines invariance with the theorem of Fubini. The key maps are shears of $G \times G$. For left invariant measures $\mu$ and $\nu$, `MeasureTheory.measurePreserving_prod_mul` says that $(x, y) \mapsto (x, x y)$ preserves $\mu \times \nu$. The lemma `MeasureTheory.measurePreserving_prod_mul_swap` treats $(x, y) \mapsto (y, y x)$, and `MeasureTheory.measurePreserving_mul_prod_inv` treats $(x, y) \mapsto (y x, x^{-1})$. The measurable equivalence `MeasurableEquiv.shearMulRight` packages the shear as a map with a measurable inverse.

These maps give a proof of the uniqueness of Haar measure. The lemma `MeasureTheory.measure_mul_measure_eq` says that for two σ-finite left invariant measures $\mu$ and $\nu$,
$$\mu(s) \, \nu(t) = \nu(s) \, \mu(t)$$
whenever $0 < \nu(s) < \infty$. So $\mu = c \nu$ with $c = \mu(s) / \nu(s)$. The intermediate step is `MeasureTheory.measure_mul_lintegral_eq`, which writes $\mu(s) \int f \, d\nu$ as an integral against $\mu$. The lemma `MeasureTheory.lintegral_lintegral_mul_inv` is the change of variables in the iterated integral.

The same tricks prove absolute continuity results. Two left invariant measures have the same null sets: `MeasureTheory.absolutelyContinuous_of_isMulLeftInvariant` says that $\mu \ll \nu$ when $\nu \ne 0$. Inversion and right multiplication are quasi measure preserving for a left invariant measure, by `MeasureTheory.quasiMeasurePreserving_inv` and `MeasureTheory.quasiMeasurePreserving_mul_right`. So $s$ is null if and only if $s^{-1}$ is null, by `MeasureTheory.measure_inv_null`. The measure need not be right invariant for this.

#### The modular character

A left Haar measure need not be right invariant. For each $g$, the image of $\mu$ under $x \mapsto x g$ is left invariant again, so it is a multiple of $\mu$ by uniqueness. The function `MeasureTheory.Measure.modularCharacterFun` gives this multiple. The lemma `MeasureTheory.Measure.map_right_mul_eq_modularCharacterFun_smul` states `map (· * g) μ = modularCharacterFun g • μ` for an inner regular Haar measure. The multiple does not depend on the choice of $\mu$. The homomorphism `MeasureTheory.Measure.modularCharacter` from `G` to `NNReal` packages it, with `MeasureTheory.Measure.modularCharacterFun_map_mul` as the main step. Its values are positive, by `MeasureTheory.Measure.modularCharacterFun_pos`. A group is unimodular when the character is trivial, for example every abelian group and every compact group.

#### The circle

The file `Mathlib.MeasureTheory.Group.Circle` gives the unit circle `Circle` of $\mathbb{C}$ its Borel σ-algebra, with `Circle.measurable_coe` and `Circle.measurable_iff`. The file `Mathlib.MeasureTheory.Group.AddCircle` works on `AddCircle T`, the quotient $\mathbb{R} / T\mathbb{Z}$ with its Haar measure. If $u$ has finite order $n$, a ball of length $T / n$ is a fundamental domain for the action of the subgroup generated by $u$: this is `AddCircle.isAddFundamentalDomain_of_ae_ball`. The lemma `AddCircle.volume_of_add_preimage_eq` then gives $\mu(s) = n \, \mu(s \cap I)$ for a set $s$ that is invariant under $u$. Section 2 treats fundamental domains in general.

#### Common errors

1. Using the multiplicative lemma on $\mathbb{R}$ or $\mathbb{R}^n$. Lebesgue measure is invariant under addition, so the lemmas have names with `add`, such as `MeasureTheory.integral_add_left_eq_self`.
2. Assuming that a left Haar measure is right invariant. Use the modular character, or prove that the group is unimodular first. Inversion is only quasi measure preserving in general.
3. Forgetting the σ-finiteness hypotheses of the product lemmas. The lemmas of `Mathlib.MeasureTheory.Group.Prod` need `SFinite` or `SigmaFinite` instances, as the theorem of Fubini does.

### Exercises

1. (A) Show that $\int_{\mathbb{R}} f(x - a) \, dx = \int_{\mathbb{R}} f(x) \, dx$ for every integrable $f$, with an additive lemma of this section.
2. (A) Show that the counting measure on a group is left invariant and right invariant.
3. (B) Show that a left invariant measure that is not zero gives positive measure to every nonempty open set, on a locally compact group with a regular measure.
4. (B) Deduce from `MeasureTheory.measure_mul_measure_eq` that two left Haar measures on a group differ by a positive constant.
5. (B) Compute the modular character of an abelian locally compact group.
6. (C) Prove that a left Haar measure on a compact group is right invariant, with the modular character and the finiteness of the measure.

### Reference

<?reference?>
