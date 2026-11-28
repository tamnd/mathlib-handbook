---
title: The spectral norm on algebraic extensions
kind: api
modules:
  - Mathlib.Analysis.Normed.Unbundled.SpectralNorm
  - Mathlib.Analysis.Normed.Unbundled.FiniteExtension
  - Mathlib.Analysis.Normed.Unbundled.InvariantExtension
  - Mathlib.Analysis.Normed.Unbundled.IsPowMulUnique
  - Mathlib.Analysis.Normed.Unbundled.GelfandRadiusNorm
explains:
  E2: [spectralValue, spectralNorm, spectralAlgNorm, spectralMulAlgNorm, spectralNorm_unique, spectralNorm.nontriviallyNormedField, exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional, IsUltrametricDist.invariantExtension, IsPowMul.unique, gelfandRadiusNorm]
  E1: auto
families: []
requires: [V06, V11, V13, V14, V16.C01, V16.C03, V16.C09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The spectral norm on algebraic extensions

### Overview

Let $K$ be a field with an ultrametric norm, for example $\mathbb{Q}_p$, and let $L$ be an algebraic extension of $K$. The norm extension theorem states that the norm of $K$ extends to $L$. The extension is the spectral norm. For a monic polynomial $p = X^d + a_{d-1} X^{d-1} + \dots + a_0$, the spectral value is the largest of the numbers $\|a_i\|^{1/(d - i)}$. The spectral norm of $y \in L$ is the spectral value of the minimal polynomial of $y$ over $K$. So the spectral norm depends only on the minimal polynomial, each automorphism of $L$ over $K$ preserves it, and it is the same for each field between $K$ and $y$.

The spectral norm is a power multiplicative algebra norm on $L$ that extends the norm of $K$, and it is the largest such norm. When $K$ is complete, it is multiplicative, it is the only power multiplicative algebra norm on $L$, and a finite extension is complete for it. Then the spectral norm of $y$ is $\|a_0\|^{1/d}$, the root of the norm of the constant term of the minimal polynomial. With this norm the algebraic closure of $\mathbb{Q}_p$ is a normed field, and the lemma of Krasner of Section 1 applies to it.

### The library around it

The module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` defines `spectralValue p` for a polynomial over a seminormed ring as the supremum of `spectralValueTerms p`. The lemma `spectralValueTerms_of_lt_natDegree` gives the term $\|a_n\|^{1/(d - n)}$ for $n < d$, and the other terms are $0$. The lemma `spectralValue_X_sub_C` states that the spectral value of $X - r$ is $\|r\|$, and `spectralValue_X_pow` states that the value of $X^n$ is $0$. For a monic polynomial, `spectralValue_eq_zero_iff` states that the value is $0$ exactly for $X^d$, and `spectralValue_le_one_iff` states that it is at most $1$ exactly when each coefficient has norm at most $1$.

The definition `spectralNorm K L y` is `spectralValue (minpoly K y)`, so it is $0$ for an element that is not algebraic. For an ultrametric normed field $K$ and an algebraic extension $L$, the main properties are the following. The lemma `spectralNorm_extends` states that the spectral norm of the image of $k \in K$ is $\|k\|$, and `spectralNorm_one` and `spectralNorm_zero` give the values at $1$ and $0$. The lemma `isPowMul_spectralNorm` states that the spectral norm is power multiplicative, and `isNonarchimedean_spectralNorm` states that it is ultrametric. The lemma `spectralNorm_eq_of_equiv` states that each automorphism of $L$ over $K$ preserves it, and `spectralNorm_zero_lt` states that it is positive at each nonzero algebraic element. The lemma `norm_le_spectralNorm` states that each power multiplicative ultrametric algebra norm $f$ on $L$ that extends the norm of $K$ is at most the spectral norm.

The definition `spectralAlgNorm K L` bundles the spectral norm as an `AlgebraNorm K L` of Section 3, with `spectralAlgNorm_def`, `spectralAlgNorm_extends` and `spectralAlgNorm_isPowMul`. For a finite normal extension, `spectralNorm_eq_iSup_of_finiteDimensional_normal` states that the spectral norm of $x$ is the supremum of $f(\sigma x)$ over the Galois group, for each norm $f$ of this kind. The form `spectralAlgNorm_of_finiteDimensional_normal` is the step of the proof for such extensions, and `spectralNorm_unique_of_finiteDimensional_normal` states the uniqueness among the norms that the Galois group preserves.

The module `Mathlib.Analysis.Normed.Unbundled.FiniteExtension` gives the first norm to start from. For a basis $B$ of a finite extension, `Module.Basis.norm` sends $x$ to the largest norm of its coordinates. The lemma `Module.Basis.norm_extends` states that it extends the norm of $K$ when $1$ is in the basis, and `Module.Basis.norm_mul_le_const_mul_norm` states that it is bounded for products with some constant $c$, but in general it is not submultiplicative. The theorem `exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional` then applies `seminormFromBounded` and `smoothingSeminorm` of Section 3 to get a power multiplicative ultrametric algebra norm on $L$ that extends the norm of $K$.

The module `Mathlib.Analysis.Normed.Unbundled.InvariantExtension` makes this norm invariant. For an automorphism $\sigma$, `IsUltrametricDist.algNormOfAlgEquiv σ` is the norm $x \mapsto f(\sigma x)$, and `IsUltrametricDist.invariantExtension K L` is the supremum of these norms over all $\sigma$. The lemmas `IsUltrametricDist.isPowMul_invariantExtension`, `IsUltrametricDist.isNonarchimedean_invariantExtension` and `IsUltrametricDist.invariantExtension_extends` state that it keeps the properties. For a finite normal extension, `spectralNorm_eq_invariantExtension` states that it is the spectral norm.

The module `Mathlib.Analysis.Normed.Unbundled.IsPowMulUnique` gives the uniqueness. Over a complete nontrivially normed field $K$, `IsPowMul.unique` states that two power multiplicative algebra norms on an algebraic extension are equal. The proof restricts the two norms to each finite subextension $K(x)$, where they are equivalent by the uniqueness of norms in finite dimension of Chapter 3, and then uses power multiplicativity to remove the constants. The forms `MulAlgebraNorm.unique` and `AlgebraNorm.toMulAlgebraNorm` follow. In `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, `spectralNorm_unique` states that each power multiplicative algebra norm is `spectralAlgNorm K L`, and `spectralNorm_unique_field_norm_ext` gives the form for an absolute value. The definition `spectralMulAlgNorm K L` is the spectral norm as a multiplicative algebra norm, and `spectralAlgNorm_mul` states that it is multiplicative. The theorem `NormedAlgebra.norm_eq_spectralNorm` states that the norm of each normed algebraic extension of $K$ is the spectral norm.

With completeness, the spectral norm gives a structure. The definitions `spectralNorm.normedField`, `spectralNorm.nontriviallyNormedField` and `spectralNorm.normedAlgebra` make $L$ a normed field and a normed algebra over $K$. They are definitions, not instances, as for the seminorms of Section 3. The instance `spectralNorm.completeSpace` states that a finite extension is complete for this norm. The theorem `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` gives the formula $\|a_0\|^{1/d}$ with the constant term of the minimal polynomial.

The module `Mathlib.Analysis.Normed.Unbundled.GelfandRadiusNorm` gives a second construction that needs no ultrametric property. For a normed field $K$ and an integral element $x$, `gelfandRadiusNorm K L x` is the Gelfand radius of Chapter 9 of the multiplication by $x$ on $K(x)$, and `gelfandRadiusNorm_eq_zero` states that the value is $0$ when $x$ is not integral. The lemma `Module.Basis.gelfandRadiusNorm_apply` computes it as the Gelfand radius of the matrix `Algebra.leftMulMatrix b x` for each basis $b$. The lemma `isPowMul_gelfandRadiusNorm` states that it is power multiplicative, `gelfandRadiusNorm_eq_norm` states that it is the norm on $K$, and `gelfandRadiusNorm_map` states that algebra maps preserve it. The definition `gelfandRadiusAlgNorm K L` bundles it as an algebra norm on an algebraic extension.

#### Common errors

1. Using `spectralNorm_unique` without completeness. Over a field that is not complete, an algebraic extension can have several power multiplicative norms that extend the norm of $K$. The theorem needs `CompleteSpace K`.
2. Forgetting that `spectralNorm K L y` is $0$ for a transcendental $y$. The properties of a norm hold only for an algebraic extension, through `Algebra.IsAlgebraic K L`.
3. Expecting the norm of a field $L$ to be the spectral norm by default. The structure `spectralNorm.nontriviallyNormedField` is a definition, so it must be made a local instance.

### Exercises

1. (A) Use `spectralValue_X_sub_C` to show that the spectral norm of an element of $K$, viewed in $L$, is its norm.
2. (A) Compute the spectral value of $X^2 - p$ over $\mathbb{Q}_p$, and deduce the spectral norm of $\sqrt{p}$.
3. (B) Show with `spectralValue_le_one_iff` that an element of $L$ has spectral norm at most $1$ if and only if its minimal polynomial has coefficients in the closed unit ball of $K$.
4. (B) Use `spectralNorm_eq_of_equiv` to show that two conjugate elements of $L$ have the same spectral norm.
5. (B) For the basis $1, i$ of $\mathbb{C}$ over $\mathbb{R}$, compute `Module.Basis.norm` at $a + b i$ and show that it is not submultiplicative.
6. (C) Use `isPowMul_gelfandRadiusNorm` and `gelfandRadius_le_norm` to show that the Gelfand radius norm of $x$ is at most the operator norm of the multiplication by $x$ for each norm on $K(x)$.

### Reference

<?reference?>
