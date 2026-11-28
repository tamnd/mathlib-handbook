---
title: Absolute value, positive parts and the logarithm in C*-algebras
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
  - Mathlib.Analysis.Real.Spectrum
explains:
  E2: [CFC.posPart_sub_negPart, CFC.posPart_mul_negPart, CFC.posPart_add_negPart, CFC.abs_mul_abs, CFC.abs_of_nonneg, IsSelfAdjoint.norm_eq_max_norm_posPart_negPart, CFC.log_exp, CFC.exp_log, SpectrumRestricts.nnreal_iff]
  E1: auto
families: []
requires: [V02, V13, V15.C05, V16]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Absolute value, positive parts and the logarithm in C*-algebras

### Overview

The real functions $x \mapsto |x|$, $x \mapsto x^+ = \max(x, 0)$, $x \mapsto x^- = \max(-x, 0)$, $\exp$ and $\log$ are elementary. The continuous functional calculus of Volume 16 applies a continuous function $f$ on the spectrum of an element $a$ of a C*-algebra and gives a new element $f(a)$. The modules of this section apply the elementary real functions in this way. The result is an absolute value $|a|$, a positive part $a^+$, a negative part $a^-$ and a logarithm $\log a$ for elements of a C*-algebra.

The main principle is simple. An identity between real functions on the spectrum gives an identity between elements. For example, $x = x^+ - x^-$ and $x^+ x^- = 0$ on $\mathbb{R}$, so $a = a^+ - a^-$ and $a^+ a^- = 0$ for each self-adjoint $a$. The proofs in this section are thus short computations with real numbers, and the library around them is a list of such transfers. The real analysis is that of Chapters 5 and 6: the order of $\mathbb{R}$, the absolute value and the real logarithm.

Read the section with one model in mind. In the C*-algebra of $n \times n$ complex matrices, a self-adjoint element is a Hermitian matrix $a = u\,\mathrm{diag}(\lambda_1, \dots, \lambda_n)\,u^*$ with $u$ unitary. Then $f(a) = u\,\mathrm{diag}(f(\lambda_1), \dots, f(\lambda_n))\,u^*$, and each statement below is a statement about the eigenvalues $\lambda_i$.

### The library around it

#### Real spectra and nonnegative spectra

The functional calculus works with several scalar rings: $\mathbb{C}$ for normal elements, $\mathbb{R}$ for self-adjoint elements and `NNReal` for nonnegative elements. The module `Mathlib.Analysis.Real.Spectrum` connects the real spectrum `spectrum` $\mathbb{R}$ $a$ with the spectrum over `NNReal`. The predicate `SpectrumRestricts` $a$ $f$ states that the spectrum of $a$ over the larger ring lies in the range of the scalar ring map, and that $f$ is a left inverse there. Here $f$ is `ContinuousMap.realToNNReal`, the map $x \mapsto \max(x, 0)$.

**Theorem.** The real spectrum of $a$ restricts to `NNReal` if and only if each $x$ in the real spectrum of $a$ satisfies $0 \le x$.

*Proof.* If the spectrum restricts, each spectral value is the image of a value in `NNReal`, so it is nonnegative. Conversely, if all spectral values are nonnegative, then $x = \max(x, 0)$ on the spectrum, and the map $x \mapsto \max(x, 0)$ is a left inverse of the inclusion there. $\square$

This is `SpectrumRestricts.nnreal_iff`. The lemma `SpectrumRestricts.nnreal_of_nonneg` applies it to an element $0 \le a$ of a C*-algebra with its order. The four lemmas `SpectrumRestricts.le_nnreal_iff`, `SpectrumRestricts.lt_nnreal_iff`, `SpectrumRestricts.nnreal_le_iff` and `SpectrumRestricts.nnreal_lt_iff` move a bound on spectral values between the two spectra. The non-unital forms use the quasispectrum `quasispectrum`, which adds the value $0$. These are `QuasispectrumRestricts.nnreal_iff`, `QuasispectrumRestricts.nnreal_of_nonneg`, `QuasispectrumRestricts.le_nnreal_iff` and `QuasispectrumRestricts.lt_nnreal_iff`. The lemma `coe_mem_spectrum_real_of_nonneg` states that for $0 \le a$ and $x$ in `NNReal`, $x$ is in the real spectrum exactly when $x$ is in the spectrum over `NNReal`.

#### Positive and negative parts

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic` defines the instances `CStarAlgebra.instPosPart` and `CStarAlgebra.instNegPart`. The unfolding lemmas are `CFC.posPart_def` and `CFC.negPart_def`: $a^+ = $ `cfcₙ` $(x \mapsto x^+)$ $a$, and the same for $a^-$. The functional calculus `cfcₙ` is the non-unital one, so the definitions work in a C*-algebra without unit. The predicate is `IsSelfAdjoint`. For an element that is not self-adjoint, the functional calculus returns the junk value $0$ (`CFC.posPart_eq_zero_of_not_isSelfAdjoint` and `CFC.negPart_eq_zero_of_not_isSelfAdjoint`).

**Theorem.** Let $a$ be self-adjoint. Then $a^+ - a^- = a$ and $a^+ a^- = a^- a^+ = 0$.

*Proof.* The functional calculus is a ring homomorphism from continuous functions on the quasispectrum. On $\mathbb{R}$, $x^+ - x^- = x$ for each $x$, because one of the two terms is $0$ and the other is $|x|$ with the sign of $x$. Also $x^+ x^- = 0$, because one of the two factors is $0$. The images of these two identities are $a^+ - a^- = $ `cfcₙ` $\mathrm{id}$ $a = a$ and $a^+ a^- = $ `cfcₙ` $0$ $a = 0$. $\square$

These are `CFC.posPart_sub_negPart`, `CFC.posPart_mul_negPart` and `CFC.negPart_mul_posPart`. Both parts are nonnegative (`CFC.posPart_nonneg` and `CFC.negPart_nonneg`), and they satisfy the bounds `CFC.le_posPart` ($a \le a^+$) and `CFC.neg_negPart_le` ($-a^- \le a$). The pair is unique.

**Theorem.** Let $a = b - c$ with $0 \le b$, $0 \le c$ and $bc = 0$. Then $a^+ = b$ and $a^- = c$.

*Proof.* The elements $b$ and $c$ commute, because $cb = (bc)^* = 0$. In the commutative C*-algebra that they generate, $b$ and $c$ are nonnegative functions with disjoint supports. On each point of the common spectrum, $b - c$ is thus $b$ or $-c$. The positive part of the function $b - c$ is $b$, and the negative part is $c$. $\square$

This is `CFC.posPart_negPart_unique`, with the halves `CFC.posPart_eq_of_eq_sub_negPart` and `CFC.negPart_eq_of_eq_PosPart_sub`. The sign rules are `CFC.posPart_eq_zero_iff` ($a^+ = 0 \iff a \le 0$), `CFC.negPart_eq_zero_iff` ($a^- = 0 \iff 0 \le a$), `CFC.posPart_eq_self` ($a^+ = a \iff 0 \le a$), `CFC.negPart_eq_neg`, `CFC.posPart_neg` ($(-a)^+ = a^-$) and `CFC.negPart_neg`. The scalar rules are `CFC.posPart_smul` and `CFC.negPart_smul` for a factor in `NNReal`, and `CFC.posPart_smul_of_nonneg`, `CFC.posPart_smul_of_nonpos`, `CFC.negPart_smul_of_nonneg` and `CFC.negPart_smul_of_nonpos` for a real factor $r$. For $r \le 0$, $(ra)^+ = (-r)\,a^-$. The values on constants are `CFC.posPart_zero`, `CFC.negPart_zero`, `CFC.posPart_one`, `CFC.negPart_one`, `CFC.posPart_natCast`, `CFC.posPart_algebraMap`, `CFC.negPart_algebraMap` and `CFC.posPart_algebraMap_nnreal`.

Each element $x$ of a C*-algebra is $\mathrm{re}\,x + i\,\mathrm{im}\,x$ with self-adjoint real part `realPart` and imaginary part. With the decomposition above, $x$ is a combination of four nonnegative elements. This is `CStarAlgebra.linear_combination_nonneg`. The consequence `CStarAlgebra.span_nonneg` states that the nonnegative elements span the whole algebra over $\mathbb{C}$. The instance `CFC.instSelfAdjointDecompose` records the decomposition for the order theory of Volume 16.

#### The norm of the two parts

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric` computes norms. In a C*-algebra, the functional calculus is isometric: $\|f(a)\| = \sup_{x} |f(x)|$, with $x$ in the spectrum of $a$.

**Theorem.** For self-adjoint $a$, $\|a\| = \max(\|a^+\|, \|a^-\|)$.

*Proof.* Let $\sigma$ be the quasispectrum of $a$, a compact subset of $\mathbb{R}$. The isometry gives $\|a\| = \sup_{x \in \sigma} |x|$, $\|a^+\| = \sup_{x \in \sigma} x^+$ and $\|a^-\| = \sup_{x \in \sigma} x^-$. For a real $x$, $|x| = \max(x^+, x^-)$. The supremum of a maximum is the maximum of the two suprema. $\square$

This is `IsSelfAdjoint.norm_eq_max_norm_posPart_negPart`. The bounds `CStarAlgebra.norm_posPart_le` and `CStarAlgebra.norm_negPart_le` state $\|a^+\| \le \|a\|$ and $\|a^-\| \le \|a\|$.

#### The absolute value

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs` defines `CFC.abs` $a$ as the square root of $a^* a$. The square root is `CFC.sqrt` of Section 6. The definition works for each element, not only for self-adjoint ones, because $a^* a$ is always nonnegative. The element `CFC.abs` $a$ is nonnegative (`CFC.abs_nonneg`).

**Theorem.** $|a|\,|a| = a^* a$ for each $a$. If $0 \le a$, then $|a| = a$.

*Proof.* The square root $s$ of a nonnegative element $b$ satisfies $s s = b$. Apply this to $b = a^* a$. For the second claim, $0 \le a$ gives $a^* = a$, so $a^* a = a a$. The element $a$ is a nonnegative square root of $a a$, and the square root is unique. So $|a| = a$. $\square$

These are `CFC.abs_mul_abs` and `CFC.abs_of_nonneg`. The variants `CFC.abs_sq` and `CFC.abs_nnrpow_two` state the same thing with a power, and `CFC.abs_nnrpow` gives $|a|^x = (a^* a)^{x/2}$. For self-adjoint $a$, the absolute value is the functional calculus of the norm: `CFC.abs_eq_cfc_norm` and `CFC.abs_eq_cfcₙ_norm`. The lemmas `cfc_comp_norm` and `cfcₙ_comp_norm` then state $f(\|\cdot\|)(a) = f(|a|)$, and `CFC.spectrum_abs` and `CFC.quasispectrum_abs` state that the spectrum of $|a|$ is the image of the spectrum of $a$ under the norm.

The link with the parts is the identity $|x| = x^+ + x^-$ on $\mathbb{R}$.

**Theorem.** For self-adjoint $a$, $a^+ + a^- = |a|$, $|a| + a = 2a^+$ and $|a| - a = 2a^-$.

*Proof.* For self-adjoint $a$, $|a| = $ `cfcₙ` $|\cdot|$ $a$. On $\mathbb{R}$, $x^+ + x^- = |x|$, $|x| + x = 2x^+$ and $|x| - x = 2x^-$. Transfer each identity with the ring homomorphism. $\square$

These are `CFC.posPart_add_negPart`, `CFC.abs_add_self` and `CFC.abs_sub_self`. The other rules match the real absolute value: `CFC.abs_zero`, `CFC.abs_one`, `CFC.abs_neg`, `CFC.abs_natCast`, `CFC.abs_intCast`, `CFC.abs_ofNat`, `CFC.abs_smul` ($|ra| = \|r\|\,|a|$), `CFC.abs_smul_nonneg`, `CFC.abs_algebraMap`, `CFC.abs_algebraMap_nnreal`, `CFC.abs_of_nonpos` ($|a| = -a$ for $a \le 0$) and `CFC.cfcAbs_cfcAbs` ($||a|| = |a|$). For a unitary element $u$ of `unitary`, $u^* u = 1$, so $|u| = 1$ (`CFC.abs_coe_unitary` and `CFC.abs_of_mem_unitary`).

Some real rules need a hypothesis. The rule $|a^*| = |a|$ is `CFC.abs_star`, and it needs a normal element, `IsStarNormal`, because $a a^*$ and $a^* a$ are different in general. The product rule `Commute.cfcAbs_mul_eq` states $|ab| = |a|\,|b|$ when $a$ commutes with $b$ and with $b^*$. The norm is the same: `CFC.norm_abs` states $\||a|\| = \|a\|$, by the C*-identity $\|a^* a\| = \|a\|^2$. Then `CFC.abs_eq_zero_iff` states $|a| = 0 \iff a = 0$, and `CFC.continuous_abs` states that $a \mapsto |a|$ is continuous on a complete algebra.

#### The exponential and the logarithm

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic` first compares two exponentials. The power series `NormedSpace.exp` of Volume 16 is defined in each Banach algebra. The functional calculus gives `cfc` `Real.exp` $a$ for self-adjoint $a$. The lemma `CFC.real_exp_eq_normedSpace_exp` states that the two agree, and `CFC.complex_exp_eq_normedSpace_exp` is the complex form for normal elements. The proof uses `NormedSpace.exp_continuousMap_eq`: on continuous functions, the power series exponential is the pointwise exponential. Then `IsSelfAdjoint.exp_nonneg` states $0 \le \exp a$.

The logarithm is `CFC.log` $a = $ `cfc` `Real.log` $a$. The real logarithm is continuous only away from $0$, so the useful hypothesis is `IsStrictlyPositive`: $a$ is self-adjoint and its spectrum lies in $(0, \infty)$.

**Theorem.** For self-adjoint $a$, $\log(\exp a) = a$. For strictly positive $a$, $\exp(\log a) = a$.

*Proof.* The functional calculus respects composition: $f(g(a)) = (f \circ g)(a)$ when $f$ is continuous on the spectrum of $g(a)$. The spectrum of $\exp a$ is $\exp$ of the spectrum of $a$, a subset of $(0, \infty)$, where $\log$ is continuous. Then $\log(\exp a) = (\log \circ \exp)(a) = \mathrm{id}(a) = a$. For the second claim, the spectrum of $a$ lies in $(0, \infty)$, where $\log$ is continuous and $\exp \circ \log = \mathrm{id}$. $\square$

These are `CFC.log_exp` and `CFC.exp_log`. The other rules are `IsSelfAdjoint.log`, `CFC.log_zero`, `CFC.log_one`, `CFC.log_algebraMap`, `CFC.log_pow`, `CFC.log_pow'`, `CFC.log_smul` and `CFC.log_smul'`. For $0 < r$ and strictly positive $a$, $\log(ra) = \log r + \log a$, with $\log r$ read as a scalar in the algebra. The rule $\log(ab) = \log a + \log b$ is absent, because it fails for elements that do not commute. Then `CFC.continuousOn_log` states that $\log$ is continuous on the set of self-adjoint units.

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order` proves that the logarithm is operator monotone and operator concave. The lemma `CFC.log_le_log` states $a \le b \implies \log a \le \log b$ for strictly positive $a$, and `CFC.log_monotoneOn` and `CFC.concaveOn_log` are the set forms. The proof does not compare spectra, because $a \le b$ gives no relation between single eigenvalues. It uses the limit $\log x = \lim_{p \to 0^+} (x^p - 1)/p$ (`CFC.tendsto_cfc_rpow_sub_one_log` and `CFC.tendsto_ite_cfc_rpow_sub_one_ite_log`), and the monotonicity and concavity of $a \mapsto a^p$ for $0 < p < 1$ from Section 6. Monotone and concave maps stay monotone and concave under a pointwise limit.

#### Common errors

1. The positive part and the negative part of an element that is not self-adjoint are $0$, a junk value of the functional calculus. Lemmas such as `CFC.posPart_sub_negPart` need the hypothesis `IsSelfAdjoint`, and this hypothesis is easy to forget for a sum or a product.
2. The function `CFC.log` needs a strictly positive element for most results. For a self-adjoint element with $0$ in the spectrum, `CFC.log` returns a value, but `CFC.exp_log` does not apply to it.
3. The real rules $|a^*| = |a|$, $|ab| = |a|\,|b|$ and $\log(ab) = \log a + \log b$ do not hold in general. Look for the form with `IsStarNormal` or with `Commute`.

### Exercises

1. (A) Let $a$ be self-adjoint. Prove $a^+ a = a^+ a^+$ from `CFC.posPart_sub_negPart` and `CFC.posPart_mul_negPart`.
2. (A) Let $a$ be the diagonal matrix $\mathrm{diag}(2, -3)$. Compute $a^+$, $a^-$ and $|a|$. Check `IsSelfAdjoint.norm_eq_max_norm_posPart_negPart` for the operator norm.
3. (B) Prove that $0 \le a$ if and only if $a$ is self-adjoint and $a^- = 0$. Use `CFC.negPart_eq_zero_iff` and `CFC.posPart_sub_negPart`.
4. (B) Let $a$ be self-adjoint. Prove $\||a|\| = \|a\|$ with the isometry of the functional calculus, without `CFC.norm_abs`.
5. (C) Find two $2 \times 2$ positive definite matrices $a$ and $b$ with $\log(ab) \ne \log a + \log b$. Explain why `CFC.log_smul'` does not contradict this example.

### Reference

<?reference?>
