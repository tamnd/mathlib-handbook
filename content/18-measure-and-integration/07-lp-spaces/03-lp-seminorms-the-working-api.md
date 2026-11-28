---
title: "Lp seminorms: the working API"
kind: api
modules:
  - Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
  - Mathlib.MeasureTheory.Function.LpSeminorm.Count
  - Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
  - Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
  - Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
  - Mathlib.MeasureTheory.Function.LpSeminorm.Prod
  - Mathlib.MeasureTheory.Function.LpSeminorm.SMul
  - Mathlib.MeasureTheory.Function.LpSeminorm.Trim
  - Mathlib.MeasureTheory.Function.Holder
  - Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
explains:
  E2: [MeasureTheory.mul_meas_ge_le_pow_eLpNorm, MeasureTheory.lpNorm, MeasureTheory.toReal_eLpNorm, MeasureTheory.eLpNorm_indicator_const, MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul, MeasureTheory.eLpNorm_trim, ContinuousLinearMap.holder, MeasureTheory.Lp.norm_smul_le]
  E1: auto
families: []
requires: [V15, V18.C04, V18.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lp seminorms: the working API

### Overview

Section 1 of this chapter defines `MeasureTheory.eLpNorm f p μ` and proves the inequalities of Hölder and Minkowski. A proof that uses $L^p$ needs many more small facts: the seminorm of an indicator function, of a scalar multiple, of a function on a restricted measure, of a function that is bounded by another one. It needs the inequality of Chebyshev and Markov in its $L^p$ form, and a version of the seminorm with real values for computations with real numbers. This section is a guide to these facts.

The facts are in several files under `Mathlib.MeasureTheory.Function.LpSeminorm` and in `Mathlib.MeasureTheory.Function.Holder`. Each file has one subject: one file for indicators, one for scalars, one for monotonicity, and so on. A learner who knows which file holds a fact can guess its name from the patterns of this section. The section needs Section 1 of this chapter, the lower Lebesgue integral of Chapter 4 and the Bochner integral of Chapter 5.

### The library around it

#### The inequality of Chebyshev and Markov

The basic tail estimate says that a function with a small $L^p$ seminorm is large only on a set of small measure. For $0 < p < \infty$ and $\varepsilon \ge 0$,
$$\varepsilon^p \, \mu\{x \mid \varepsilon \le \|f(x)\|\} \le \|f\|_p^p.$$

The file `Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov` states this in several forms. All of them work in `ENNReal`, with the extended norm `‖f x‖ₑ`.

| Lean name | Statement |
|---|---|
| `MeasureTheory.mul_meas_ge_le_pow_eLpNorm` | $\varepsilon \, \mu\{\varepsilon \le \|f\|^p\} \le \|f\|_p^p$ |
| `MeasureTheory.mul_meas_ge_le_pow_eLpNorm'` | $\varepsilon^p \, \mu\{\varepsilon \le \|f\|\} \le \|f\|_p^p$ |
| `MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm` | the bound solved for the measure, with the factor `ε⁻¹ ^ p.toReal` |
| `MeasureTheory.MemLp.meas_ge_lt_top` | for `f` in $L^p$ and `ε ≠ 0`, the set where $\varepsilon \le \|f\|$ has finite measure |

The hypotheses `p ≠ 0` and `p ≠ ⊤` appear in each statement. For $p = \infty$ the right estimate is different: the set where $\|f\|$ exceeds the essential supremum is null. The last lemma is the reason why a function in $L^p$ with $p < \infty$ is concentrated on a σ-finite set. The file `Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp` uses it to prove `MeasureTheory.Lp.finStronglyMeasurable`: an element of $L^p$ for $0 < p < \infty$ is the limit of simple functions with supports of finite measure. The lemmas `MeasureTheory.MemLp.aefinStronglyMeasurable` and `MeasureTheory.Integrable.aefinStronglyMeasurable` are the forms for functions. Chapter 10 needs them for the conditional expectation.

#### A real-valued seminorm

The seminorm `eLpNorm` takes values in $[0, \infty]$. This is the right choice for the theory, because every function has a seminorm and no integrability hypothesis is needed to state a bound. For computations with real numbers it is awkward. The file `Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm` defines `MeasureTheory.lpNorm f p μ : ℝ`, the real number $\|f\|_p$. The lemma `MeasureTheory.toReal_eLpNorm` says that it is `(eLpNorm f p μ).toReal`. It is zero when $f$ is not in $L^p$, by `MeasureTheory.lpNorm_of_not_memLp`, and when $f$ is not almost everywhere strongly measurable, by `MeasureTheory.lpNorm_of_not_aestronglyMeasurable`.

The main rules for `lpNorm` are:

| Lean name | Statement |
|---|---|
| `MeasureTheory.lpNorm_nonneg` | `0 ≤ lpNorm f p μ` |
| `MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal` | for $0 < p < \infty$, $\|f\|_p = (\int \|f\|^p \, d\mu)^{1/p}$ as a Bochner integral |
| `MeasureTheory.lpNorm_one_eq_integral_norm` | $\|f\|_1 = \int \|f\| \, d\mu$ |
| `MeasureTheory.lpNorm_add_le` | the triangle inequality for $1 \le p$, if `f` is in $L^p$ |
| `MeasureTheory.lpNorm_const_smul` | homogeneity under a scalar |
| `MeasureTheory.lpNorm_exponent_top_eq_essSup` | for $p = \infty$, the essential supremum of the norm |

The triangle inequality needs a hypothesis that `eLpNorm` does not need. If `f` is not in $L^p$, then `lpNorm f p μ = 0`, and the inequality can fail. This is the price of the real values. A good rule is to prove bounds with `eLpNorm` and to convert to `lpNorm` only at the end.

#### Indicators and restrictions

The file `Mathlib.MeasureTheory.Function.LpSeminorm.Indicator` computes the seminorm of a function that is zero outside a set. The lemma `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict` says that the seminorm of `s.indicator f` for `μ` is the seminorm of `f` for `μ.restrict s`, for a null measurable set `s`. The lemma `MeasureTheory.eLpNorm_indicator_const` computes $\|c \, \mathbf{1}_s\|_p = \|c\| \, \mu(s)^{1/p}$ for $0 < p < \infty$. The lemmas `MeasureTheory.eLpNorm_indicator_le` and `MeasureTheory.eLpNorm_restrict_le` say that cutting a function to a set does not increase its seminorm.

The lemma `MeasureTheory.MemLp.exists_eLpNorm_indicator_compl_lt` is a form of the tightness of a single function. For `f` in $L^p$ with $p < \infty$ and every $\varepsilon > 0$, there is a measurable set $s$ of finite measure with $\|\mathbf{1}_{s^c} f\|_p < \varepsilon$. Section 5 of this chapter extends this to families of functions.

The predicates are also stable: `MeasureTheory.MemLp.indicator` says that the indicator of a function in $L^p$ is in $L^p$, and `MeasureTheory.memLp_indicator_iff_restrict` states the converse with the restricted measure. The lemma `MeasureTheory.MemLp.piecewise` treats a function defined by two cases.

#### Comparison and monotonicity

A bound between two functions gives a bound between their seminorms. The file `Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity` has lemmas of the form "if `‖f x‖ ≤ c * ‖g x‖` almost everywhere, then `eLpNorm f p μ ≤ c * eLpNorm g p μ`". The main one is `MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul`, with a real constant `c`. Its consequence for the predicate is `MeasureTheory.MemLp.of_le_mul`: if `g` is in $L^p$, `f` is almost everywhere strongly measurable, and `‖f x‖ ≤ c * ‖g x‖` almost everywhere, then `f` is in $L^p$. The versions with a prime or with `nnreal` in the name take the constant in `NNReal` or work with extended norms.

The same file proves that complex conjugation, `star`, the real part and the imaginary part preserve $L^p$: see `MeasureTheory.eLpNorm_conj`, `MeasureTheory.MemLp.star`, `MeasureTheory.MemLp.re` and `MeasureTheory.MemLp.im`.

#### Scalars

The file `Mathlib.MeasureTheory.Function.LpSeminorm.SMul` proves `MeasureTheory.eLpNorm_const_smul`: the seminorm of `c • f` is `‖c‖ₑ * eLpNorm f p μ`, under the class `NormSMulClass`. Without this class only the inequality `MeasureTheory.eLpNorm_const_smul_le` holds. The predicate versions are `MeasureTheory.MemLp.const_smul`, `MeasureTheory.MemLp.const_mul` and `MeasureTheory.MemLp.mul_const`. For functions with values in `ENNReal` the lemma `MeasureTheory.eLpNorm_const_mul_ennreal` plays the same role.

#### Products, counting measure and trimmed measures

The file `Mathlib.MeasureTheory.Function.LpSeminorm.Prod` has two lemmas. `MeasureTheory.MemLp.comp_fst` says that if `f` is in $L^p(\mu)$ and `ν` is a finite measure, then `fun x ↦ f x.1` is in $L^p(\mu \otimes \nu)$. `MeasureTheory.MemLp.comp_snd` is the same for the second factor.

The file `Mathlib.MeasureTheory.Function.LpSeminorm.Count` treats the counting measure and Dirac masses. The lemma `MeasureTheory.eLpNorm_dirac` says that the seminorm for `Measure.dirac i` is `‖f i‖ₑ`. The lemma `MeasureTheory.eNorm_le_eLpNorm_count` bounds each value by the seminorm for the counting measure, and `MeasureTheory.eLpNorm_count_lt_top` says that on a finite type every function with finite values is in $L^p$.

The file `Mathlib.MeasureTheory.Function.LpSeminorm.Trim` compares a measure `μ` on a σ-algebra `m0` with its restriction `μ.trim hm` to a smaller σ-algebra `m`. The lemma `MeasureTheory.eLpNorm_trim` says that the two seminorms agree for a function that is strongly measurable for `m`. The lemma `MeasureTheory.memLp_of_memLp_trim` transfers the predicate. These lemmas are the base of the construction of the conditional expectation in Chapter 10, which works in $L^2$ of the trimmed measure.

#### The inequality of Hölder for bilinear maps

Section 1 proves the inequality of Hölder for products of real functions. The file `Mathlib.MeasureTheory.Function.Holder` states it for a continuous bilinear map `B : E →L[𝕜] F →L[𝕜] G`. The exponents are related by the class `ENNReal.HolderTriple p q r`, which says $1/p + 1/q = 1/r$. The lemma `MeasureTheory.eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm` says that the $L^r$ seminorm of `fun x ↦ B (f x) (g x)` is at most `‖B‖ₑ * eLpNorm f p μ * eLpNorm g q μ`. The lemma `ContinuousLinearMap.memLp_of_bilin` gives the predicate.

On the spaces of classes, `ContinuousLinearMap.holder` is the map $L^p \times L^q \to L^r$ that `B` induces. The bundled versions `ContinuousLinearMap.holderₗ` and `ContinuousLinearMap.holderL` are bilinear and continuous bilinear maps. For $r = 1$ and a complete target, `ContinuousLinearMap.lpPairing` composes with the integral and gives a continuous pairing between $L^p$ and $L^q$, and `ContinuousLinearMap.lpPairing_eq_integral` computes it. With the scalar multiplication as the bilinear map, the file defines the product `f • g` of an element of $L^p$ with values in `𝕜` and an element of $L^q$, and proves `MeasureTheory.Lp.norm_smul_le`: $\|f \cdot g\|_r \le \|f\|_p \|g\|_q$.

#### Common errors

1. Using `MeasureTheory.lpNorm_add_le` without the hypothesis `MemLp f p μ`. The real seminorm of a function outside $L^p$ is zero, so the triangle inequality needs this hypothesis. Prove the bound for `eLpNorm` first.
2. Applying the inequality of Chebyshev and Markov with `p = ⊤`. The lemmas need `p ≠ ⊤`. For $p = \infty$ use the bound of a function by its essential supremum.
3. Forgetting that `MeasureTheory.eLpNorm_trim` needs strong measurability for the smaller σ-algebra. A function measurable only for `m0` has a different seminorm for the trimmed measure, often a larger one.

### Exercises

1. (A) Compute `eLpNorm (s.indicator fun _ ↦ (2 : ℝ)) 3 μ` for a measurable set `s` with `μ s = 8`.
2. (A) Show that for $f$ in $L^1(\mu)$ and $t > 0$, $\mu\{x \mid t \le |f(x)|\} \le \|f\|_1 / t$, with the lemmas of this section.
3. (B) Show that if $f \in L^p(\mu)$ and $g$ is measurable with $|g| \le |f|$ almost everywhere, then $g \in L^p(\mu)$ and $\|g\|_p \le \|f\|_p$ in `lpNorm`.
4. (B) Give a function $f$ and an exponent $p$ such that `lpNorm (f + f) p μ ≤ lpNorm f p μ + lpNorm f p μ` holds but `MemLp f p μ` fails. Explain why the triangle inequality is still stated with the hypothesis.
5. (B) Use `ContinuousLinearMap.lpPairing` to show that the map $(f, g) \mapsto \int f g \, d\mu$ is continuous on $L^2 \times L^2$.
6. (C) Prove that an element of $L^p$ with $1 \le p < \infty$ vanishes outside a σ-finite set, with `MeasureTheory.MemLp.meas_ge_lt_top`.

### Reference

<?reference?>
