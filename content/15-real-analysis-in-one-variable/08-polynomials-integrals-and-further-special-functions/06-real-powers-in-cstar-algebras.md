---
title: Real powers and square roots in C*-algebras
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
  - Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
explains:
  E2: [CFC.sqrt_unique, CFC.rpow_add, CFC.rpow_rpow, CFC.norm_sqrt, CFC.conjSqrt_ringInverse_self, Real.rpowIntegrand₀₁_eq_pow_div, Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const, CFC.rpow_le_rpow]
  E1: auto
families: []
requires: [V02, V13, V15.C05, V15.C06, V16]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Real powers and square roots in C*-algebras

### Overview

Chapter 6 defines the real power $x^y$ for $x \ge 0$ and $y \in \mathbb{R}$. The continuous functional calculus of Volume 16 applies this function to a nonnegative element $a$ of a C*-algebra. The result is a real power $a^y$ and a square root $\sqrt{a} = a^{1/2}$. These powers are basic tools of operator theory. The square root gives the absolute value of Section 5, the polar decomposition and the characterization of nonnegative elements as the elements $b^* b$.

Most identities transfer from $\mathbb{R}$ in one line, because the functional calculus is a ring homomorphism that respects composition. The order results are different. The relation $a \le b$ does not compare single eigenvalues, so a monotone real function need not give a monotone map $a \mapsto f(a)$. The map $a \mapsto a^2$ is the standard counterexample. For $0 \le p \le 1$, the map $a \mapsto a^p$ is monotone and concave all the same. The proof writes $x^p$ as an integral of functions of the form $x/(t + x)$, and each such function is operator monotone. This integral representation is a piece of real analysis on $(0, \infty)$, and it is the main real content of this section.

The model is again the algebra of $n \times n$ complex matrices. A nonnegative element is a positive semidefinite matrix $u\,\mathrm{diag}(\lambda_1, \dots, \lambda_n)\,u^*$ with $\lambda_i \ge 0$, and $a^y = u\,\mathrm{diag}(\lambda_1^y, \dots, \lambda_n^y)\,u^*$.

### The library around it

#### Definitions and the two exponent types

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic` has two powers. The first is `CFC.nnrpow` with an exponent $y$ in `NNReal`: $a^y = $ `cfcₙ` $(x \mapsto x^y)$ $a$, with the real function `NNReal.nnrpow` (`NNReal.nnrpow_def`). The functional calculus `cfcₙ` is the non-unital one, so this power works without a unit. The second is `CFC.rpow` with a real exponent: $a^y = $ `cfc` $(x \mapsto x^y)$ $a$. This power needs a unit, because $x^y$ for $y < 0$ is not $0$ at $x = 0$. The instances `CFC.instPowNNReal` and `CFC.instPowReal` give the notation `a ^ y` for both, and `CFC.nnrpow_def`, `CFC.rpow_def`, `CFC.nnrpow_eq_pow` and `CFC.rpow_eq_pow` unfold it. The lemmas `CFC.rpow_eq_cfc_real` and `CFC.nnrpow_eq_cfcₙ_real` restate the definitions with the real functional calculus.

The two powers differ at the exponent $0$. The non-unital calculus sends each function to a function with value $0$ at $0$, so `CFC.nnrpow_zero` states $a^0 = 0$. The unital power has `CFC.rpow_zero`: $a^0 = 1$ for $0 \le a$. For $0 < y$ the two powers agree (`CFC.nnrpow_eq_rpow`). The square root is `CFC.sqrt` $a = $ `cfcₙ` `NNReal.sqrt` $a$, with `CFC.sqrt_eq_cfc`, `CFC.sqrt_eq_real_sqrt`, `CFC.sqrt_eq_nnrpow` and `CFC.sqrt_eq_rpow` ($\sqrt{a} = a^{1/2}$).

All these functions need a nonnegative element. For an element that is not nonnegative, they return the junk value $0$ (`CFC.sqrt_of_not_nonneg`).

#### Laws of exponents

The real laws transfer when the real functions agree on the spectrum.

**Theorem.** Let $a$ be a nonnegative unit. Then $a^{x+y} = a^x a^y$. If $a$ is strictly positive, then $(a^x)^y = a^{xy}$.

*Proof.* For a unit, $0$ is not in the spectrum. On $(0, \infty)$, $t^{x+y} = t^x t^y$, and the functional calculus is multiplicative. This gives the first claim. For the second claim, the spectrum of $a^x$ is the image of the spectrum of $a$ under $t \mapsto t^x$, a subset of $(0, \infty)$. Composition gives $(a^x)^y = (t \mapsto (t^x)^y)(a) = (t \mapsto t^{xy})(a)$. $\square$

These are `CFC.rpow_add` and `CFC.rpow_rpow`. The spectrum rule is `CFC.spectrum_rpow`, and `CFC.cfc_rpow` composes the power with an arbitrary function. Without the unit, the rule $a^{x+y} = a^x a^y$ fails for $x + y = 0$: the left side is $1$ and the right side is not $1$ if $0$ is in the spectrum. The rule for `CFC.nnrpow` needs $0 < x$ and $0 < y$ (`CFC.nnrpow_add`). The other laws are `CFC.nnrpow_nnrpow`, `CFC.rpow_rpow_of_exponent_nonneg`, `CFC.rpow_inv_rpow`, `CFC.rpow_rpow_inv`, `CFC.nnrpow_inv_nnrpow`, `CFC.nnrpow_nnrpow_inv` and `CFC.nnrpow_inv_eq`.

The integer exponents give the usual powers: `CFC.rpow_one`, `CFC.rpow_natCast`, `CFC.rpow_intCast`, `CFC.nnrpow_one`, `CFC.nnrpow_two` ($a^2 = aa$) and `CFC.nnrpow_three`. The negative exponents give inverses: `CFC.rpow_neg`, `CFC.rpow_neg_one_eq_inv`, `CFC.rpow_neg_one_eq_cfc_inv`, `CFC.rpow_mul_rpow_neg` and `CFC.rpow_neg_mul_rpow`. The inverse `Ring.inverse` is $a^{-1}$ for a unit and $0$ for other elements, and `CFC.inverse_rpow` and `CFC.inverse_eq_rpow_neg_one` connect it with the powers. The bundled unit is `Units.cfcRpow`, with `Units.val_cfcRpow` and `Units.val_inv_cfcRpow`. The unit rules are `IsUnit.cfcRpow`, `IsUnit.cfcNNRpow`, `CFC.isUnit_rpow_iff` and `CFC.isUnit_nnrpow_iff`. The values on constants are `CFC.zero_rpow`, `CFC.zero_nnrpow`, `CFC.one_rpow` and `CFC.rpow_algebraMap`. Positivity is preserved: `CFC.rpow_nonneg`, `CFC.nnrpow_nonneg`, `CFC.sqrt_nonneg`, `IsStrictlyPositive.rpow`, `IsStrictlyPositive.nnrpow` and `IsStrictlyPositive.sqrt`.

#### The square root

**Theorem.** Let $0 \le b$ and $bb = a$. Then $\sqrt{a} = b$.

*Proof.* The spectrum of $b$ lies in $[0, \infty)$. By composition, $\sqrt{a} = \sqrt{bb} = (t \mapsto \sqrt{t^2})(b)$. On $[0, \infty)$, $\sqrt{t^2} = t$, so $\sqrt{a} = \mathrm{id}(b) = b$. $\square$

This is `CFC.sqrt_unique`, with `CFC.sqrt_eq_iff` and `CFC.mul_self_eq`. The existence half is `CFC.sqrt_mul_sqrt_self` ($\sqrt{a}\sqrt{a} = a$ for $0 \le a$), with `CFC.sq_sqrt` and `CFC.nnrpow_sqrt_two`. The other direction is `CFC.sqrt_mul_self` ($\sqrt{aa} = a$ for $0 \le a$), with `CFC.sqrt_sq` and `CFC.sqrt_nnrpow_two`. Uniqueness gives cancellation of squares: `CFC.mul_self_eq_mul_self_iff` and `CFC.sq_eq_sq_iff` state $aa = bb \iff a = b$ for nonnegative $a$ and $b$. The values are `CFC.sqrt_zero`, `CFC.sqrt_one`, `CFC.sqrt_eq_zero_iff`, `CFC.sqrt_eq_one_iff` and `CFC.sqrt_algebraMap`. The mixed rules are `CFC.sqrt_rpow`, `CFC.rpow_sqrt`, `CFC.nnrpow_sqrt`, `CFC.sqrt_nnrpow`, `CFC.rpow_sqrt_nnreal` and `CFC.sqrt_rpow_nnreal`. For units, `CFC.isUnit_sqrt_iff`, `CFC.isUnit_sqrt_iff_isStrictlyPositive`, `IsStrictlyPositive.isUnit_cfcSqrt` and `CFC.sqrt_ringInverse` hold.

The square root gives the list of equivalent forms of nonnegativity. The theorem `CStarAlgebra.nonneg_tfae` states that, in a C*-algebra, the following are equivalent: $0 \le a$; $a = \sqrt{a}\sqrt{a}$; $a = bb$ for some $0 \le b$; $a = bb$ for some self-adjoint $b$; $a = b^* b$ for some $b$; $a = b b^*$ for some $b$; and $a$ is self-adjoint with $a^- = 0$. The separate directions are `CStarAlgebra.nonneg_iff_eq_sqrt_mul_sqrt`, `CStarAlgebra.nonneg_iff_exists_nonneg_and_eq_mul_self`, `CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self`, `CStarAlgebra.nonneg_iff_eq_star_mul_self`, `CStarAlgebra.nonneg_iff_eq_mul_star_self` and `CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero`. The strict form is `CStarAlgebra.isStrictlyPositive_tfae`, with `CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self`: $a$ is strictly positive if and only if $a = b^* b$ for a unit $b$. The lower-case names `CStarAlgebra.nonneg_tfae` and `CStarAlgebra.isStrictlyPositive_tfae` are the same lists in the form of the TFAE tactic. Products and families have their own rules: `CFC.sqrt_map_prod`, `CFC.sqrt_map_pi`, `CFC.rpow_map_prod`, `CFC.rpow_map_pi`, `CFC.nnrpow_map_prod` and `CFC.nnrpow_map_pi`.

#### Norms, continuity and measurability

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric` uses the isometry of the functional calculus.

**Theorem.** For $0 \le a$, $\|\sqrt{a}\| = \sqrt{\|a\|}$.

*Proof.* Let $\sigma \subseteq [0, \infty)$ be the spectrum of $a$. The isometry gives $\|a\| = \sup_{t \in \sigma} t$ and $\|\sqrt{a}\| = \sup_{t \in \sigma} \sqrt{t}$. The function $\sqrt{\cdot}$ is continuous and increasing, so it commutes with the supremum of a compact set. $\square$

This is `CFC.norm_sqrt`, with `CFC.nnNorm_sqrt`. The same argument gives `CFC.norm_rpow` ($\|a^r\| = \|a\|^r$ for $0 < r$), `CFC.nnNorm_rpow`, `CFC.norm_nnrpow` and `CFC.nnNorm_nnrPow`. The C*-identity then gives `CFC.norm_star_mul_mul_self_of_nonneg`: $\|b^* a b\| = \|\sqrt{a}\,b\|^2$ for $0 \le a$, with `CFC.norm_mul_mul_star_self_of_nonneg`, `CFC.IsSelfAdjoint.norm_mul_mul_self_of_nonneg` and `CFC.IsSelfAdjoint.norm_mul_mul_self_of_nonneg'`. The continuity lemmas are `CFC.continuousOn_sqrt` on the nonnegative elements, `CFC.continuousOn_nnrpow` and `CFC.continuousOn_rpow` on the strictly positive elements. The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable` has one result, `CFC.measurable_sqrt`, for an algebra with a Borel structure.

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt` defines the continuous real-linear map `CFC.conjSqrt` $c$: $a \mapsto \sqrt{c}\,a\,\sqrt{c}$ (`CFC.conjSqrt_apply` and `CFC.toLinearMap_conjSqrt`). It is monotone (`CFC.conjSqrt_monotone` and `CFC.conjSqrt_le_conjSqrt`), because $\sqrt{c}$ is self-adjoint and $x \le y$ gives $s x s \le s y s$ for self-adjoint $s$. It sends $1$ to $c$ (`CFC.conjSqrt_one`), and it is $0$ when $c$ is not nonnegative (`CFC.conjSqrt_of_not_nonneg`).

**Theorem.** For strictly positive $c$, $\sqrt{c^{-1}}\;c\;\sqrt{c^{-1}} = 1$.

*Proof.* The elements $c$ and $\sqrt{c^{-1}}$ are both functions of $c$, so they commute. The product is $(t \mapsto t^{-1/2}\,t\,t^{-1/2})(c) = 1$, because $t^{-1/2} t\, t^{-1/2} = 1$ for $t > 0$. $\square$

This is `CFC.conjSqrt_ringInverse_self`. The maps `CFC.conjSqrt` $c$ and `CFC.conjSqrt` $c^{-1}$ are inverse to each other (`CFC.conjSqrt_conjSqrt_ringInverse` and `CFC.conjSqrt_ringInverse_conjSqrt`). Then `CFC.isStrictlyPositive_conjSqrt_iff` and `CFC.ringInverse_conjSqrt` hold. The map reduces an inequality $a \le b$ with $b$ strictly positive to an inequality $\sqrt{b^{-1}}\,a\,\sqrt{b^{-1}} \le 1$.

#### Convexity of the inverse

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder` proves `CStarAlgebra.convexOn_ringInverse`: the map $a \mapsto a^{-1}$ is convex on the strictly positive elements. The corollary `CStarAlgebra.convexOn_ringInverse_algebraMap_add` states that, for $t > 0$, the map $x \mapsto (t + x)^{-1}$ is convex on the nonnegative elements. The monotone half, $a \le b \implies b^{-1} \le a^{-1}$, is in Volume 16. Both halves feed the integral representation below.

#### The integral representation

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation` begins with three real integrands, for $t > 0$ and $x \ge 0$:
$$f_p(t, x) = t^p\bigl(t^{-1} - (t + x)^{-1}\bigr), \qquad g_p(t, x) = t^{p-1}\bigl(t^{-1}x + t(t + x)^{-1} - 1\bigr), \qquad h_p(t, x) = t^p (t + x)^{-1}.$$
These are `Real.rpowIntegrand₀₁`, `Real.rpowIntegrand₁₂` and `Real.rpowIntegrandNeg`. The subscripts give the range of $p$: $(0, 1)$, $(1, 2)$ and $(-1, 0)$.

**Theorem.** For $t > 0$ and $x \ge 0$, $f_p(t, x) = t^{p-1}\,x/(t + x)$.

*Proof.* $t^{-1} - (t + x)^{-1} = \bigl((t + x) - t\bigr)/\bigl(t(t + x)\bigr) = x/\bigl(t(t + x)\bigr)$. Multiply by $t^p$ and use $t^p/t = t^{p-1}$. $\square$

This is `Real.rpowIntegrand₀₁_eq_pow_div`, with `Real.rpowIntegrand₀₁_eq_sub`. The form shows $0 \le f_p$ (`Real.rpowIntegrand₀₁_nonneg`), and $f_p(t, \cdot)$ is increasing (`Real.rpowIntegrand₀₁_monotoneOn`). Near $t = 0$, $f_p(t, x) \le t^{p-1}$ (`Real.rpowIntegrand₀₁_le_rpow_sub_one`). Near $t = \infty$, $f_p(t, x) \le t^{p-2} x$ (`Real.rpowIntegrand₀₁_le_rpow_sub_two_mul_self`). For $0 < p < 1$, the first bound is integrable on $(0, 1]$ and the second on $[1, \infty)$. This gives `Real.integrableOn_rpowIntegrand₀₁_Ioi`, and `Real.integral_rpowIntegrand₀₁_one_pos` states $\int_0^\infty f_p(t, 1)\,dt > 0$, with the lower bound `Real.le_integral_rpowIntegrand₀₁_one`.

**Theorem.** For $0 < p < 1$ and $x \ge 0$, $\int_0^\infty f_p(t, x)\,dt = x^p \int_0^\infty f_p(t, 1)\,dt$.

*Proof.* For $x = 0$ both sides are $0$. For $x > 0$, substitute $t = xs$, $dt = x\,ds$. Then
$$f_p(xs, x) = (xs)^{p-1}\frac{x}{xs + x} = x^{p-1} s^{p-1}\frac{1}{s + 1} = x^{p-1} f_p(s, 1).$$
With the factor $x$ from $dt$, the integral is $x^p \int_0^\infty f_p(s, 1)\,ds$. $\square$

This is `Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const`, with the scaling lemmas `Real.rpowIntegrand₀₁_apply_mul`, `Real.rpowIntegrand₀₁_apply_mul'` and `Real.rpowIntegrand₀₁_eqOn_mul_rpowIntegrand₀₁_one`. Division by the positive constant gives `Real.rpow_eq_const_mul_integral`: $x^p = C_p^{-1} \int_0^\infty f_p(t, x)\,dt$. The constant is $C_p = \pi/\sin(p\pi)$, but the library does not compute it, and no proof needs its value. The other ranges reduce to this one: `Real.rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁` writes $g_p$ with $x\,f_{p-1}$, and `Real.rpowIntegrandNeg_eq_inv_mul_rpowIntegrand₀₁` writes $h_p$ with $f$ and $x^{-1}$. The results are `Real.rpow_eq_const_mul_integral_rpowIntegrand₁₂` for $1 < p < 2$ and `Real.rpow_eq_const_mul_integral_rpowIntegrandNeg` for $-1 < p < 0$. The measure forms `Real.exists_measure_rpow_eq_integral_rpowIntegrand₀₁`, `Real.exists_measure_rpow_eq_integral_rpowIntegrand₁₂` and `Real.exists_measure_rpow_eq_integral_rpowIntegrandNeg` absorb the constant and the weight into a measure $\mu$ on $(0, \infty)$.

The algebra versions apply the functional calculus under the integral: `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`, `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂` and `CFC.exists_measure_rpow_eq_integral_cfc_rpowIntegrand₁₀`. For each $t > 0$, $f_p(t, a) = t^p\bigl(t^{-1} - (t + a)^{-1}\bigr)$ as an element. If $a \le b$, then $(t + b)^{-1} \le (t + a)^{-1}$, so $f_p(t, a) \le f_p(t, b)$. This is `CFC.monotoneOn_cfcₙ_rpowIntegrand₀₁`. The convexity of $x \mapsto (t + x)^{-1}$ gives `CFC.concaveOn_cfcₙ_rpowIntegrand₀₁` and `CFC.concaveOn_cfc_rpowIntegrand₀₁`. An integral against a positive measure keeps both properties.

#### Operator monotonicity and concavity

The module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order` collects the result.

**Theorem.** Let $0 \le p \le 1$ and $0 \le a \le b$. Then $a^p \le b^p$.

*Proof.* For $p = 0$ both sides are $1$, and for $p = 1$ the claim is $a \le b$. For $0 < p < 1$, $a^p = \int_0^\infty f_p(t, a)\,d\mu(t)$ with a positive measure $\mu$. Each integrand is monotone in $a$, and integration against $\mu$ keeps the order. $\square$

This is `CFC.rpow_le_rpow`, with `CFC.nnrpow_le_nnrpow`, `CFC.monotone_rpow`, `CFC.monotone_nnrpow`, `CFC.monotone_sqrt` and `CFC.sqrt_le_sqrt`. The concavity results are `CFC.concaveOn_rpow`, `CFC.concaveOn_nnrpow` and `CFC.concaveOn_sqrt` on `Set.Ici` $0$. For $p > 1$ the map is not monotone in general, and the theorem has no form for such $p$.

#### Common errors

1. The power `CFC.nnrpow` with exponent $0$ is $0$, not $1$, because the non-unital functional calculus fixes the value $0$ at $0$. Use `CFC.rpow` with a real exponent when $a^0 = 1$ is needed.
2. The functions `CFC.sqrt`, `CFC.rpow` and `CFC.nnrpow` return $0$ on an element that is not nonnegative. A lemma with an automatic hypothesis $0 \le a$ tries to prove it with a tactic, and it fails for an element with no visible proof of nonnegativity.
3. The rule $a^p \le b^p$ holds only for $0 \le p \le 1$. The rule $a \le b \implies a^2 \le b^2$ is false for matrices, and so is $\sqrt{ab} = \sqrt{a}\sqrt{b}$ for elements that do not commute.

### Exercises

1. (A) Prove $\sqrt{a^2} = a$ for $0 \le a$ from `CFC.sqrt_unique` and `CFC.nnrpow_two`.
2. (A) Compute $\int_0^\infty f_{1/2}(t, 1)\,dt$ by hand with the substitution $t = s^2$. Check the value $\pi$ against the formula $C_p = \pi/\sin(p\pi)$.
3. (B) Find $2 \times 2$ real symmetric matrices with $0 \le a \le b$ and $a^2 \not\le b^2$. Hint: try $a = \mathrm{diag}(1, 0)$ and a matrix $b$ with all entries positive.
4. (B) Let $c$ be strictly positive. Prove that $a \le c$ if and only if $\sqrt{c^{-1}}\,a\,\sqrt{c^{-1}} \le 1$. Use `CFC.conjSqrt_monotone`, `CFC.conjSqrt_ringInverse_self` and `CFC.conjSqrt_conjSqrt_ringInverse`.
5. (C) Prove that $f_p(t, \cdot)$ is concave on $[0, \infty)$ for each $t > 0$, and deduce from `Real.rpow_eq_const_mul_integral` that $x \mapsto x^p$ is concave on $[0, \infty)$ for $0 < p < 1$.

### Reference

<?reference?>
