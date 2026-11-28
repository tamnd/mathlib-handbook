---
title: Measurable algebraic operations and special functions
kind: api
modules:
  - Mathlib.MeasureTheory.Group.Arithmetic
  - Mathlib.MeasureTheory.Group.MeasurableEquiv
  - Mathlib.MeasureTheory.Group.Pointwise
  - Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
  - Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
  - Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
  - Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
  - Mathlib.MeasureTheory.Constructions.AddChar
  - Mathlib.MeasureTheory.Function.Floor
  - Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
  - Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
  - Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
  - Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
  - Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
explains:
  E2: [MeasurableMul₂.toMeasurableMul, Measurable.mul, measurable_inv_iff, MeasurableSet.const_smul, Real.measurable_of_measurable_exp, measurable_of_re_im]
  E1: auto
families: []
requires: [V04, V05, V13]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Measurable algebraic operations and special functions

### Overview

Section 3 proved that sums, products and limits of measurable real functions are measurable. A user of Mathlib meets the same question in many other types: a group, a vector space, the complex numbers, a space of continuous maps, the extended reals. Mathlib does not prove the rules again for each type. It states them once for a type with a measurable operation, and it records the measurability of the operation in a class. This section explains these classes, the rules that follow from them, and the instances for the common types of analysis.

The second half of the section lists the measurability results for the elementary functions: the exponential, the logarithm, the trigonometric functions, the argument of a complex number, the floor function and the inner product. Each of them is continuous or piecewise continuous, so the result is easy on paper. The lemmas exist so that a proof of measurability is one call of the tactic `measurability` or of `fun_prop`, and they are the leaves of such a search.

### The library around it

#### Classes of measurable operations

The module `Mathlib.MeasureTheory.Group.Arithmetic` has two classes for each binary operation. For a multiplication on a measurable space $M$:

| Lean name | Statement |
|---|---|
| `MeasurableMul` | for each $c$, the maps $x \mapsto c x$ and $x \mapsto x c$ are measurable |
| `MeasurableMul₂` | the map $(x, y) \mapsto x y$ is measurable on $M \times M$ |
| `MeasurableInv` | the map $x \mapsto x^{-1}$ is measurable |
| `MeasurableDiv` | for each $c$, the maps $x \mapsto c / x$ and $x \mapsto x / c$ are measurable |
| `MeasurableDiv₂` | the map $(x, y) \mapsto x / y$ is measurable on $M \times M$ |
| `MeasurablePow` | the map $(x, n) \mapsto x^n$ is measurable on $M \times N$ |
| `MeasurableConstSMul` | for each $c$, the map $x \mapsto c \cdot x$ is measurable |
| `MeasurableSMul` | the maps $x \mapsto c \cdot x$ and $c \mapsto c \cdot x$ are measurable |
| `MeasurableSMul₂` | the map $(c, x) \mapsto c \cdot x$ is measurable |

Each class has an additive twin with the same pattern: `MeasurableAdd`, `MeasurableAdd₂`, `MeasurableNeg`, `MeasurableSub`, `MeasurableSub₂`, `MeasurableConstVAdd`, `MeasurableVAdd` and `MeasurableVAdd₂`. The two levels exist because the product σ-algebra on $M \times M$ can be smaller than the Borel σ-algebra of the product topology. For a topological group that is not second countable, the multiplication is continuous but need not be measurable for the product σ-algebra. Then only the weaker class holds.

**Proposition (The strong class gives the weak one).** If $(x, y) \mapsto x y$ is measurable, then $x \mapsto c x$ and $x \mapsto x c$ are measurable for each $c$.

*Proof.* The map $x \mapsto (c, x)$ is measurable into $M \times M$, because its two components are a constant and the identity (Section 3). The map $x \mapsto c x$ is the composite of this map with the multiplication. The other side uses $x \mapsto (x, c)$. $\square$

This is the instance `MeasurableMul₂.toMeasurableMul`. In the same way `MeasurableDiv₂.toMeasurableDiv` and `MeasurableSMul₂.toMeasurableSMul` hold. In a group the division is $x y^{-1}$, so `measurableDiv₂_of_mul_inv` builds `MeasurableDiv₂` from `MeasurableMul₂` and `MeasurableInv`. The power instances are `Monoid.measurablePow` for natural exponents and `DivInvMonoid.measurableZPow` for integer exponents. A monoid acts on itself, and `measurableSMul_of_mul` turns `MeasurableMul M` into `MeasurableSMul M M`.

The instances propagate through the constructions of algebra. `Pi.measurableMul` gives a product of types the operation coordinate by coordinate. `MulOpposite.instMeasurableMul` treats the opposite monoid, `Units.instMeasurableSpace` gives the units of a monoid the σ-algebra pulled back from $M \times M$, and `Subgroup.instMeasurableSMul` restricts an action to a subgroup. On a type where every set is measurable, `DiscreteMeasurableSpace.toMeasurableMul₂` and its siblings give all the classes at once.

#### The rules for measurable functions

With the classes in place, the rules of Section 3 take one form for every type. Let $f, g : \alpha \to M$ be measurable.

**Proposition (Products of measurable functions).** If `MeasurableMul₂ M` holds, then $x \mapsto f(x) g(x)$ is measurable.

*Proof.* The map $x \mapsto (f(x), g(x))$ is measurable into $M \times M$ by the universal property of the product σ-algebra. Compose it with the multiplication. $\square$

This is `Measurable.mul`. A product with a constant needs only the weak class: `Measurable.const_mul` and `Measurable.mul_const` assume `MeasurableMul M`. The names follow the pattern of the algebra library. `Measurable.add`, `Measurable.sub`, `Measurable.div`, `Measurable.inv`, `Measurable.neg` and `Measurable.pow` treat the other operations, and `Measurable.smul`, `Measurable.const_smul` and `Measurable.smul_const` treat an action. A lemma whose last component starts with fun, such as `Measurable.fun_mul`, states the same result with the function written as a lambda, $x \mapsto f(x) g(x)$, instead of `f * g`; the two forms help the automation in different situations. The versions with a prime, such as `Measurable.mul'`, treat functions of two variables. Finite sums and products follow: `Finset.measurable_sum`, `Finset.measurable_prod`, `List.measurable_prod` and `Multiset.measurable_sum`.

Each rule has a twin for almost everywhere measurable functions with the prefix `AEMeasurable`, such as `AEMeasurable.mul` and `AEMeasurable.const_smul`. Chapter 2 defines these functions, and the twins are in the same module.

**Proposition (Inversion does not change measurability).** If `MeasurableInv G` holds and the inversion is an involution, then $f$ is measurable if and only if $x \mapsto f(x)^{-1}$ is measurable.

*Proof.* One direction is composition with the inversion. For the other, $f$ is the composite of $x \mapsto f(x)^{-1}$ with the inversion, because $(y^{-1})^{-1} = y$. $\square$

This is `measurable_inv_iff`. The same argument with $c^{-1}$ gives `measurable_const_smul_iff` for an action of a group, and `IsUnit.measurable_const_smul_iff` for an action of a unit of a monoid. In a commutative group `Measurable.mul_iff_left` says that $g f$ is measurable if and only if $g$ is, when $f$ is measurable.

#### Measurable equivalences of a group

The module `Mathlib.MeasureTheory.Group.MeasurableEquiv` bundles the bijections of a group as measurable equivalences `G ≃ᵐ G`. The left translation is `MeasurableEquiv.mulLeft g`, the right translation is `MeasurableEquiv.mulRight g`, and the inversion is `MeasurableEquiv.inv G`. The divisions give `MeasurableEquiv.divLeft` and `MeasurableEquiv.divRight`. For an action of a group on a type $\alpha$, `MeasurableEquiv.smul g` is the map $x \mapsto g \cdot x$ of $\alpha$. In a group with zero, the forms `MeasurableEquiv.mulLeft₀` and `MeasurableEquiv.smul₀` need $g \ne 0$. The simp lemmas such as `MeasurableEquiv.symm_mulLeft` identify the inverse: the inverse of the left translation by $g$ is the left translation by $g^{-1}$. The unbundled forms `measurableEmbedding_mulLeft`, `measurableEmbedding_const_smul` and `measurableEmbedding_inv` give measurable embeddings, which transport measurable sets in both directions.

The same module lets a group act on the measures of a space through the type `Gᵈᵐᵃ` of the action on the domain, and `MeasureTheory.Measure.domSMul_apply` states $(g \cdot \mu)(s) = \mu(g^{-1} \cdot s)$ in this form. Chapter 9 uses this action for invariant measures.

**Proposition (Translates of measurable sets).** If a group $G$ acts on $\alpha$ and each map $x \mapsto c \cdot x$ is measurable, then $a \cdot s$ is measurable for each measurable $s$ and each $a \in G$.

*Proof.* The set $a \cdot s$ is the preimage of $s$ under $x \mapsto a^{-1} \cdot x$, because $x \in a \cdot s$ if and only if $a^{-1} \cdot x \in s$. This map is measurable by the hypothesis. $\square$

This is `MeasurableSet.const_smul`, from `Mathlib.MeasureTheory.Group.Pointwise`. The version `MeasurableSet.const_smul₀` treats a group with zero, where the scalar $0$ needs that singletons are measurable. The module `Mathlib.MeasureTheory.Group.Arithmetic` has `MeasurableSet.inv` for the set $s^{-1}$.

#### Borel structures on types of analysis

Several modules give a common type its Borel σ-algebra and prove the instance `BorelSpace`. `Complex.borelSpace` treats $\mathbb{C}$, and `RCLike.borelSpace` treats any field of the class `RCLike`, that is $\mathbb{R}$ or $\mathbb{C}$. The module on `RCLike` proves `RCLike.measurable_re`, `RCLike.measurable_im` and `RCLike.measurable_ofReal`.

**Proposition (Complex functions by parts).** A function $f : \alpha \to \mathbb{C}$ is measurable if its real part and its imaginary part are measurable.

*Proof.* The map $z \mapsto (\operatorname{Re} z, \operatorname{Im} z)$ is a homeomorphism $\mathbb{C} \to \mathbb{R}^2$. The space $\mathbb{R}^2$ is second countable, so its Borel σ-algebra is the product σ-algebra. The pair $(\operatorname{Re} f, \operatorname{Im} f)$ is measurable into the product, and $f$ is its composite with the inverse homeomorphism, which is continuous and hence measurable. $\square$

This is `measurable_of_re_im`, stated for any `RCLike` field.

The module `Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap` gives the space `E →L[𝕜] F` of continuous linear maps its Borel σ-algebra, with the instance `ContinuousLinearMap.instBorelSpace`. A continuous linear map is measurable (`ContinuousLinearMap.measurable`), and the evaluation at a point $x$ is measurable as a function of the map (`ContinuousLinearMap.measurable_apply`). The lemma `measurable_smul_const` says that $x \mapsto f(x) \cdot c$ is measurable if and only if $f$ is, for a fixed vector $c \ne 0$.

The module `Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap` gives the space `C(X, Y)` of continuous maps its Borel σ-algebra for the compact open topology (the instance `ContinuousMap.measurableSpace`). The main result `ContinuousMap.borel_eq_iSup_comap_eval` says that this σ-algebra is the smallest one for which every evaluation $f \mapsto f(x)$ is measurable, when $X$ and $Y$ are second countable, $X$ is locally compact and $Y$ is regular. A practical form is `ContinuousMap.measurable_iff_eval`: a map into `C(X, Y)` is measurable if and only if each of its evaluations is measurable.

The module `Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop` treats `WithTop ι`, an order with a top element added, such as $[0, \infty]$ built from $[0, \infty)$. The equivalence `WithTop.measurableEquivSum` identifies `WithTop ι` with the sum of $\iota$ and a point, and `WithTop.MeasurableEquiv.neTopEquiv` identifies the set $\{r \ne \top\}$ with $\iota$. The lemmas `Measurable.withTop_coe` and `Measurable.untopD` pass a measurable function in and out of `WithTop`. The small module `Mathlib.MeasureTheory.Constructions.AddChar` gives the type of additive characters of a finite group the discrete σ-algebra, with the instances `AddChar.instMeasurableSpace` and `AddChar.instDiscreteMeasurableSpace`.

#### Special functions

The module `Mathlib.MeasureTheory.Function.SpecialFunctions.Basic` proves that the elementary functions are measurable. The pattern of the names is fixed. For the real function `Real.exp` there is `Real.measurable_exp`, and for a composite $x \mapsto \exp(f(x))$ there is `Measurable.exp`. The same pairs exist for `log`, `sin`, `cos`, `sinh`, `cosh`, `arcsin` and `arccos`, and `Measurable.sqrt` treats the square root. The complex functions have the prefix `c` in the composite form: `Complex.measurable_exp` and `Measurable.cexp`, `Complex.measurable_log` and `Measurable.clog`, and `Complex.measurable_arg` and `Measurable.carg`. The instances `Real.hasMeasurablePow`, `NNReal.hasMeasurablePow`, `ENNReal.hasMeasurablePow` and `Complex.hasMeasurablePow` make the real and complex powers measurable in both variables.

The logarithm and the argument are not continuous on all of their domain, but they are continuous outside a measurable set, so they are still measurable. The exponential also gives a converse.

**Proposition (Measurability through the exponential).** If $x \mapsto e^{f(x)}$ is measurable for a real $f$, then $f$ is measurable.

*Proof.* For a real $y$, $\log(e^y) = y$. So $f$ is the composite of $x \mapsto e^{f(x)}$ with the logarithm, which is measurable. $\square$

This is `Real.measurable_of_measurable_exp`.

The smaller modules complete the list. `Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan` has `Real.measurable_arctan` and `Measurable.arctan`. `Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc` has `Real.measurable_sinc` and `Measurable.sinc` for $\operatorname{sinc} x = \sin x / x$, and also `Real.integrable_sinc` on a finite measure. `Mathlib.MeasureTheory.Function.SpecialFunctions.Inner` has `Measurable.inner`, `Measurable.const_inner` and `Measurable.inner_const` for the inner product of two measurable functions into an inner product space, when the space is second countable. `Mathlib.MeasureTheory.Function.Floor` treats the floor and the fractional part on an ordered ring with a floor: `Int.measurable_floor`, `Nat.measurable_floor`, `Int.measurable_ceil`, `measurable_fract`, their composite forms `Measurable.floor` and `Measurable.fract`, and `MeasurableSet.image_fract`, which says that the image of a measurable set under $x \mapsto x - \lfloor x \rfloor$ is measurable.

#### Common errors

1. A learner uses `Measurable.mul` on a type with only `MeasurableMul`. The instance search then fails with a message about `MeasurableMul₂`. Use `Measurable.const_mul` when one factor is constant, or prove that the space is second countable so that the strong class holds.
2. A learner writes `Real.measurable_exp.comp hf` and gets a goal with a composite `Real.exp ∘ f`. The lemma `Measurable.exp` gives the form $x \mapsto \exp(f(x))$ at once, and the tactics `measurability` and `fun_prop` find it.
3. A learner expects the Borel σ-algebra of `C(X, Y)` to be generated by the evaluations for every pair of spaces. The equality `ContinuousMap.borel_eq_iSup_comap_eval` needs the countability and regularity hypotheses.

### Exercises

1. (A) Prove from `MeasurableMul₂` that $x \mapsto x^2$ is measurable on $M$.
2. (A) Show that $x \mapsto \lfloor x \rfloor$ is Borel measurable on $\mathbb{R}$ by writing the preimage of each set as a countable union of intervals.
3. (A) Let $f, g : \alpha \to \mathbb{R}$ be measurable with $g > 0$. Show that $x \mapsto f(x)^{g(x)}$ is measurable, with the instance `Real.hasMeasurablePow`.
4. (B) Show that the map $f \mapsto f(x)$ is measurable on `E →L[𝕜] F` from the continuity of evaluation, and explain why this does not need second countability.
5. (B) Let $G$ act measurably on $\alpha$. Show that the set $\{x : g \cdot x \in s\}$ is measurable for a measurable $s$, and compare it with $g^{-1} \cdot s$.
6. (C) Show that $\arg : \mathbb{C} \to \mathbb{R}$ is Borel measurable: it is continuous outside the closed half line $(-\infty, 0]$, and it is constant on that half line minus the origin.

### Reference

<?reference?>
