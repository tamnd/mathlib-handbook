---
title: Order, norm and continuity of the functional calculus
kind: api
modules:
  - Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
  - Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
  - Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
  - Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
  - Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
  - Mathlib.Analysis.CStarAlgebra.Commutative.PosPart
  - Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
  - Mathlib.Analysis.CStarAlgebra.Fuglede
  - Mathlib.Analysis.InnerProductSpace.Abs
  - Mathlib.Analysis.InnerProductSpace.StarOrder
explains:
  E2: [CStarAlgebra.spectralOrder, CStarAlgebra.norm_le_norm_of_le_of_nonneg, CStarAlgebra.inv_le_inv_iff, IsometricContinuousFunctionalCalculus, norm_cfc_le_iff, Continuous.cfc, fuglede_putnam_rosenblum, CStarAlgebra.exists_sum_four_nonneg, ContinuousLinearMap.abs, ContinuousLinearMap.instStarOrderedRing]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C06, V16.C07, V16.C09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Order, norm and continuity of the functional calculus

### Overview

An element $a$ of a C*-algebra is positive, written $0 \le a$, when it is self-adjoint and its spectrum is in $[0, \infty)$. The following conditions are equivalent: $a$ is positive, $a = b^* b$ for some $b$, and $a = c^2$ for a self-adjoint $c$. The positive elements form a closed convex cone, and $a \le b$ means $0 \le b - a$. This is a partial order, compatible with addition and with the maps $x \mapsto c^* x c$. So a C*-algebra is a star ordered ring. On $B(H)$, the order is the usual order of operators: $S \le T$ if and only if $\langle x, S x \rangle \le \langle x, T x \rangle$ for all $x$.

The functional calculus of Section 2 interacts with the norm and with the order. For a normal $a$ and a continuous $f$ on its spectrum, $\|f(a)\| = \sup_{z \in \sigma(a)} |f(z)|$, since the calculus is an isometry from $C(\sigma(a))$. For a positive $a$, $\|a\|$ is the largest point of the spectrum, so $a \le \|a\| \cdot 1$. On the positive cone, the norm is monotone: $0 \le a \le b$ gives $\|a\| \le \|b\|$. A proof: $b \le \|b\| \cdot 1$ and $a \le b$ give $a \le \|b\| \cdot 1$, which says that the spectrum of $a$ is in $[0, \|b\|]$.

The order is not as simple as the order of functions. If $0 \le a \le b$, then $a^2 \le b^2$ fails in general, already for $2 \times 2$ matrices. But some functions are operator monotone. The inverse is one: if $0 < a \le b$ with $a$ invertible, then $b^{-1} \le a^{-1}$. A proof: conjugate by $a^{-1/2}$ to get $1 \le a^{-1/2} b a^{-1/2}$, which says that the spectrum of $c = a^{-1/2} b a^{-1/2}$ is in $[1, \infty)$. Then $c^{-1} \le 1$ by the functional calculus, and the conjugation by $a^{-1/2}$ takes this back to $b^{-1} \le a^{-1}$. The square root is also operator monotone.

Two other results belong here. The Fuglede Putnam theorem says that if $a$ and $b$ are normal and $x a = b x$, then $x a^* = b^* x$. In particular, an element that commutes with a normal $a$ also commutes with $a^*$. And each element of a C*-algebra is a combination $x_0 + i x_1 - x_2 - i x_3$ of four positive elements with norm at most $\|a\|$: write $a$ as a sum of its real and imaginary parts, then write each self-adjoint part as the difference of its positive and negative parts.

### The library around it

The order on a C*-algebra is not an instance in Mathlib, since some C*-algebras, such as `ℂ` and `C(X, ℂ)`, have their own order already. The definition `CStarAlgebra.spectralOrder` gives the partial order by spectrum, and `CStarAlgebra.spectralOrderedRing` shows that it makes `A` a star ordered ring. Both are in `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic`. For a new C*-algebra, the user puts these in place as local instances, or proves `StarOrderedRing A` directly. For operators on a Hilbert space, the file `Mathlib.Analysis.InnerProductSpace.StarOrder` gives the instance `ContinuousLinearMap.instStarOrderedRing`, where the order is the one of `ContinuousLinearMap.IsPositive`, and `ContinuousLinearMap.IsPositive.spectrumRestricts` says that a positive operator has spectrum in $[0, \infty)$.

The file `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order` proves the order facts for any C*-algebra with `StarOrderedRing A`. The cone is closed by `CStarAlgebra.isClosed_nonneg`. The lemmas `IsSelfAdjoint.le_algebraMap_norm_self` and `CStarAlgebra.norm_le_iff_le_algebraMap` compare an element with a multiple of `1`, and `CStarAlgebra.norm_mem_spectrum_of_nonneg` says that the norm of a positive element is in its spectrum. The lemma `CStarAlgebra.star_mul_le_algebraMap_norm_sq` gives $a^* a \le \|a\|^2$. Monotonicity of the norm is `CStarAlgebra.norm_le_norm_of_le_of_nonneg`, and `IsSelfAdjoint.norm_le_max_of_le_of_le` bounds a self-adjoint element between two others. `CStarAlgebra.mem_Icc_iff_norm_le_one` describes the order interval from $0$ to $1$. For conjugation, `CStarAlgebra.star_left_conjugate_le_norm_smul` gives $a^* b a \le \|b\| a^* a$. For inverses, `CStarAlgebra.inv_le_inv_iff` is the operator monotonicity of the inverse, `CStarAlgebra.antitoneOn_ringInverse` is the same statement for `Ring.inverse` on the strictly positive elements, and `CStarAlgebra.isUnit_of_le` says that an element above a strictly positive one is invertible. The predicate `IsStrictlyPositive` is positivity together with invertibility, and `IsStrictlyPositive.of_le` and `isStrictlyPositive_add` are its closure lemmas. The lemma `CStarAlgebra.pow_monotone` says that $n \mapsto a^n$ is monotone for $1 \le a$, and `le_iff_norm_sqrt_mul_rpow` gives a norm test for $a \le b$ with `CFC.sqrt` and a power of `b`.

The file `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric` adds the class `IsometricContinuousFunctionalCalculus R A p`, which says that `cfcHom` is an isometry, `isometry_cfcHom`. The three standard instances of Section 2 satisfy it in a C*-algebra. The lemmas `norm_cfc_le_iff` and `norm_cfc_lt_iff` reduce a bound on `‖cfc f a‖` to a bound on `f` over the spectrum, and `IsGreatest.norm_cfc` says that the norm is attained. `CFC.norm_pow` gives $\|a^n\| = \|a\|^n$ for an element in the domain of the calculus.

The file `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity` treats `cfc f a` as a function of `a` and of `f`. The lemma `Continuous.cfc` says that if `x ↦ a x` is continuous and the spectra stay in a fixed compact set near each point, then `x ↦ cfc f (a x)` is continuous. Forms with filters and with sets are `Filter.Tendsto.cfc`, `ContinuousOn.cfc` and `continuousOn_cfc`. In the function argument, `lipschitzOnWith_cfc_fun` says that `f ↦ cfc f a` is $1$-Lipschitz for the uniform norm on the spectrum. The file `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral` moves the calculus inside a Bochner integral with `cfc_integral` and `cfc_setIntegral`, under a domination hypothesis. This is the tool for integral formulas such as $a^{1/2} = \pi^{-1} \int_0^\infty t^{-1/2} a (t + a)^{-1} \, dt$.

The file `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart` connects the calculus to the decomposition $a = \operatorname{Re} a + i \operatorname{Im} a$. For a normal `a`, `spectrum_realPart` says that the spectrum of the real part is the image of the spectrum of `a` under $z \mapsto \operatorname{Re} z$, and `cfc_realPart` and `cfc_imaginaryPart` compute the calculus of the parts.

The file `Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart` proves `CStarAlgebra.exists_sum_four_nonneg`, the decomposition into four positive elements, and deduces `CStarAlgebra.span_nonneg_inter_closedBall`: the positive elements of norm at most $r$ span the whole algebra. The file `Mathlib.Analysis.CStarAlgebra.Commutative.PosPart` proves that the positive part $a^+$ is monotone in a commutative C*-algebra, `CStarAlgebra.posPart_mono`, and that the negative part is antitone, `CStarAlgebra.negPart_anti`. Without commutativity these statements are false.

The file `Mathlib.Analysis.CStarAlgebra.Fuglede` proves `fuglede_putnam_rosenblum`, stated with `SemiconjBy x a b` for $x a = b x$. The proof uses the theorem of Liouville. Let $f(z) = e^{z b^*} x e^{-z a^*}$. From $x a = b x$, the element $x$ also intertwines $e^{\bar z a}$ and $e^{\bar z b}$, so $f(z) = u x v$, where normality makes $u$ and $v$ exponentials of $i$ times self-adjoint elements, which are unitary by Section 1. So $\|f(z)\| = \|x\|$ for all $z$. The function $f$ is entire and bounded, so it is constant, and its derivative at $0$ gives $b^* x - x a^* = 0$. The lemma `IsStarNormal.commute_star_right` is the special case $a = b$. A consequence is `CStarAlgebra.isMulCommutative_adjoin`: a set of pairwise commuting normal elements generates a commutative C*-subalgebra.

The file `Mathlib.Analysis.InnerProductSpace.Abs` defines the absolute value of an operator between Hilbert spaces, `ContinuousLinearMap.abs`, by `ContinuousLinearMap.abs_def`: $|T| = (T^* T)^{1/2}$ with `CFC.sqrt`. For an operator on one space, `ContinuousLinearMap.abs_eq_cfcAbs` says that it agrees with `CFC.abs`. The lemma `ContinuousLinearMap.norm_abs_apply` gives $\| |T| x \| = \|T x\|$, the key step for the polar decomposition, and `ContinuousLinearMap.ker_abs` says that $|T|$ and $T$ have the same kernel.

#### Common errors

1. A lemma with `[StarOrderedRing A]` does not apply to a general C*-algebra until an order is in place. For an abstract `A`, add `CStarAlgebra.spectralOrder A` and `CStarAlgebra.spectralOrderedRing A` as local instances.
2. Monotonicity of $x \mapsto x^2$ is false for the operator order. `CStarAlgebra.pow_monotone` is about the exponent, not the base, and `CStarAlgebra.posPart_mono` needs a commutative algebra.
3. `Continuous.cfc` needs a uniform control of the spectra, not only continuity of `a`. Without it the conclusion can fail, because `cfc f` jumps to `0` where `f` is not continuous on the spectrum.

### Exercises

1. (A) Prove that $\|a\| \le 1$ for $0 \le a \le 1$, with `CStarAlgebra.mem_Icc_iff_norm_le_one`.
2. (A) Show that $a^* a \le \|a\|^2 \cdot 1$ in a C*-algebra with `CStarAlgebra.star_mul_le_algebraMap_norm_sq`, and deduce $\|a^* a\| \le \|a\|^2$.
3. (B) Find two positive $2 \times 2$ real matrices with $a \le b$ and not $a^2 \le b^2$.
4. (B) Prove that $1 \le a$ implies $a^{-1} \le 1$ for an invertible positive `a`, with `CStarAlgebra.inv_le_inv_iff`.
5. (B) Show that the norm of `cfc (fun x ↦ x ^ 2) a` is $\|a\|^2$ for a self-adjoint `a`, with `norm_cfc_le_iff` and `IsGreatest.norm_cfc`.
6. (C) Use `fuglede_putnam_rosenblum` to prove that the product of two commuting normal elements is normal.

### Reference

<?reference?>
