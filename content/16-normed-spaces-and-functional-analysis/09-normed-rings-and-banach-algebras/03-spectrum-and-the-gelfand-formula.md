---
title: Spectrum and the Gelfand formula
kind: api
modules:
  - Mathlib.Analysis.Normed.Algebra.Basic
  - Mathlib.Analysis.Normed.Algebra.Spectrum
  - Mathlib.Analysis.Normed.Algebra.GelfandRadius
  - Mathlib.Analysis.Normed.Algebra.GelfandFormula
  - Mathlib.Analysis.Normed.Algebra.GelfandMazur
  - Mathlib.Analysis.Matrix.GelfandRadius
explains:
  E2: [spectralRadius, spectrum.isCompact, spectrum.norm_le_norm_of_mem, gelfandRadius, tendsto_gelfandRadius, spectrum.nonempty, spectrum.gelfand_formula, NormedRing.algEquivComplexOfComplete, NormedAlgebra.Complex.nonempty_algEquiv, Matrix.gelfandRadius_mul_comm]
  E1: auto
families: []
requires: [V06, V07, V13, V16.C01, V16.C02, V16.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Spectrum and the Gelfand formula

### Overview

The spectrum of an element $a$ of an algebra $A$ over a field $\mathbb{K}$ is the set of scalars $k$ such that $k \cdot 1 - a$ is not a unit. For a matrix it is the set of eigenvalues. For an operator on an infinite dimensional space it can contain more points, since an injective operator need not be surjective. In a complete normed algebra the spectrum is compact and lies in the closed ball of radius $\|a\|$. Over $\mathbb{C}$ it is also nonempty, and its largest absolute value, the spectral radius, is given by the formula of Gelfand: $\rho(a) = \lim_n \|a^n\|^{1/n}$.

From the nonempty spectrum comes the theorem of Gelfand and Mazur: a complex Banach algebra in which each nonzero element is a unit is $\mathbb{C}$. Mathlib also has a second proof that needs no completeness, but a multiplicative norm. The limit $\lim_n \|a^n\|^{1/n}$ exists in each normed ring, and Mathlib calls it the Gelfand radius. This section gives the spectrum, the spectral radius, the Gelfand radius and the link between them.

### The library around it

The sets `spectrum 𝕜 a` and `resolventSet 𝕜 a` and the map `resolvent a k`, the inverse of $k \cdot 1 - a$, are defined in the algebra volumes. The lemma `spectrum.mem_iff` states that $k$ is in the spectrum if and only if $k \cdot 1 - a$ is not a unit. For an algebra without a unit, `quasispectrum 𝕜 a` is the version that Chapter 12 uses for the functional calculus. The module `Mathlib.Analysis.Normed.Algebra.Spectrum` adds the norm. In a complete normed algebra, `spectrum.norm_le_norm_of_mem` states that $\|k\| \le \|a\|$ for each $k$ in the spectrum, and `spectrum.subset_closedBall_norm` states the same as an inclusion. The spectrum is closed, by `spectrum.isClosed`, since the units form an open set, and it is compact, by `spectrum.isCompact`. The instance `spectrum.instCompactSpace` gives the same as a class.

The spectral radius `spectralRadius 𝕜 a` is the supremum of $\|k\|$ over the spectrum, in the extended nonnegative reals, so the spectral radius of an element with empty spectrum is $0$. The lemma `spectralRadius_eq_of_unital` gives this form, and `spectralRadius_smul` states that $\rho(c a) = \|c\| \rho(a)$. The lemma `spectrum.mem_resolventSet_of_spectralRadius_lt` states that $k$ is in the resolvent set when $\rho(a) < \|k\|$. The lemma `isUnit_one_sub_smul_of_lt_inv_spectralRadius` states that $1 - z a$ is a unit when $\|z\| < \rho(a)^{-1}$. The lemma `upperHemicontinuous_spectrum` states that the spectrum depends upper hemicontinuously on $a$: a small change of $a$ cannot make the spectrum much larger.

The spectrum of an element of a subalgebra can be larger than its spectrum in the algebra, since fewer elements are units. The lemma `Subalgebra.frontier_spectrum_subset_spectrum` states that the boundary of the spectrum in a closed subalgebra lies in the spectrum in the algebra. The lemma `Subalgebra.spectrum_eq_of_isPreconnected_compl` states that the two spectra are equal when the complement of the spectrum in the algebra is connected, which holds for example for a real spectrum.

The module `Mathlib.Analysis.Normed.Algebra.GelfandRadius` defines `gelfandRadius a` as the limit of $\|a^n\|^{1/n}$ in a seminormed ring. The theorem `tendsto_gelfandRadius` states that the limit exists, by a lemma of Fekete on subadditive sequences. The lemma `gelfandRadius_le_norm` states that $r(a) \le \|a\|$, and `gelfandRadius_le_norm_pow` states that $r(a) \le \|a^n\|^{1/n}$ for each $n \ge 1$. The lemma `gelfandRadius_pow` states that $r(a^n) = r(a)^n$, and `gelfandRadius_smul` states that $r(c a) = \|c\| r(a)$. For commuting elements, `Commute.gelfandRadius_add_le` and `Commute.gelfandRadius_mul_le` give the subadditivity and the submultiplicativity. The lemma `norm_pow_le_mul_pow_of_gelfandRadius_lt` gives the converse bound: for $r > r(a)$ there is $C$ with $\|a^n\| \le C r^n$ for all $n$.

The module `Mathlib.Analysis.Normed.Algebra.GelfandFormula` uses complex analysis. The resolvent is differentiable on the resolvent set, by `spectrum.hasDerivAt_resolvent_const_left`, and it tends to $0$ at infinity, by `resolvent_isBigO_cobounded_inv`. If the spectrum were empty, the resolvent would be a bounded entire function that tends to $0$, so it would be $0$ by the theorem of Liouville, which is false. This proves `spectrum.nonempty` for a nontrivial complex Banach algebra. The theorem `spectrum.gelfand_formula` states that $\|a^n\|^{1/n} \to \rho(a)$. The theorem `spectrum.spectralRadius_eq_gelfandRadius` states that the spectral radius equals the Gelfand radius. The lemma `spectrum.map_polynomial_aeval` is the spectral mapping theorem for polynomials: the spectrum of $p(a)$ is the image of the spectrum of $a$ under $p$.

The theorem of Gelfand and Mazur has two forms. The equivalence `NormedRing.algEquivComplexOfComplete` takes a complete normed complex algebra in which each nonzero element is a unit, and gives an algebra isomorphism from $\mathbb{C}$. The module `Mathlib.Analysis.Normed.Algebra.GelfandMazur` proves the second form. The theorem `NormedAlgebra.Complex.nonempty_algEquiv` states that a nontrivial normed complex algebra with a multiplicative norm is $\mathbb{C}$, and `NormedAlgebra.Complex.algEquivOfNormMul` gives the isomorphism. The proof minimizes $z \mapsto \|x - z \cdot 1\|$ and uses roots of unity in place of complex analysis. The real form `NormedAlgebra.Real.nonempty_algEquiv_or` states that a normed field that is a normed real algebra is $\mathbb{R}$ or $\mathbb{C}$.

The module `Mathlib.Analysis.Normed.Algebra.Basic` uses the spectrum for characters. A character of an algebra is a nonzero algebra homomorphism to $\mathbb{K}$, and the characters form the character space `WeakDual.characterSpace 𝕜 A`. Since $\varphi(a)$ is in the spectrum of $a$, `WeakDual.CharacterSpace.norm_toStrongDual_le_one` states that each character has norm at most $1$. With the theorem of Banach and Alaoglu of Chapter 5, the character space is compact over a proper field, by the instance `WeakDual.CharacterSpace.instCompactSpaceElemCharacterSpaceOfProperSpace`. The module also gives the instance `IntermediateField.instNontriviallyNormedFieldSubtypeMem`, which makes each intermediate field of a normed extension a nontrivially normed field.

The last module computes Gelfand radii of matrices with the operator norm. The theorem `Matrix.gelfandRadius_mul_comm` states that $r(A B) = r(B A)$, also for rectangular matrices. The theorem `Matrix.gelfandRadius_blockDiagonal` states that the radius of a block diagonal matrix is the largest radius of a block. The theorem `LinearMap.gelfandRadius_toMatrix_eq` states that the radius of the matrix of a linear map does not depend on the basis.

#### Common errors

1. Using `spectrum.nonempty` over $\mathbb{R}$. A rotation of $\mathbb{R}^2$ by a right angle has empty real spectrum. The theorem needs a complex algebra.
2. Treating `spectralRadius 𝕜 a` as a real number. It is in `ENNReal`. Use `ENNReal.toReal`, or use `gelfandRadius a`, which is real, and `spectrum.spectralRadius_eq_gelfandRadius` to pass between the two.
3. Expecting the spectrum in a closed subalgebra to equal the spectrum in the algebra. It can be larger, since the subalgebra has fewer units. Use `Subalgebra.spectrum_eq_of_isPreconnected_compl` when the complement of the spectrum is connected.

### Exercises

1. (A) Compute `spectrum ℂ A` for the matrix $A = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ and show that $r(A) = 0$ with `gelfandRadius_le_norm_pow`.
2. (A) Show with `spectrum.norm_le_norm_of_mem` that the spectrum of an element of norm less than $1$ lies in the open unit disc.
3. (B) Use `gelfandRadius_pow` and `gelfandRadius_le_norm` to show that $r(a) = 0$ for each nilpotent $a$.
4. (B) For the matrices $A = \begin{pmatrix} 1 & 0 \end{pmatrix}$ and $B = \begin{pmatrix} 0 \\ 1 \end{pmatrix}$, compute $A B$ and $B A$, and check `Matrix.gelfandRadius_mul_comm` on them.
5. (B) Show that $|\varphi(a)| \le \|a\|$ for each character $\varphi$ of a complex Banach algebra, since $\varphi(a)$ is in the spectrum of $a$. Compare with `WeakDual.CharacterSpace.norm_toStrongDual_le_one`.
6. (C) Prove `spectrum.nonempty` for $2 \times 2$ complex matrices from the existence of a root of the characteristic polynomial, and compare with the proof by the theorem of Liouville.

### Reference

<?reference?>
